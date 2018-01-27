package server;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;

import net.Protocol;
import net.Protocol.Extensions;
import net.Protocol.Packets;
import net.ProtocolViolatedException;

/**
 * This class is a separate thread for the server to keep track of a connection with
 * one specific client. This <code>ClientHandler</code> does <b>not</b> handle game
 * input (moving). These packets are forwarded to a <code>GameManager</code>.
 */
public class ClientHandler implements Runnable {

	private final RinggzServer server;
	private final Socket clientSocket;
	private final BufferedReader in;
	private final BufferedWriter out;
	
	private String clientUsername;
	private String[] extensions;
	
	/**
	 * Lobby that the client of this handler is currently in. If this field is <code>null</code>,
	 * the client is currently not in a lobby.
	 */
	private GameManager game;
	
	private boolean responded;
	private boolean ready;
	
	/**
	 * The player type of the client of this handler.
	 */
	private String playerType;
	
	public ClientHandler(RinggzServer server, Socket clientSocket) throws IOException {
		this.server = server;
		this.clientSocket = clientSocket;
		this.in = new BufferedReader(new InputStreamReader(this.clientSocket.getInputStream(), "UTF-8"));
        this.out = new BufferedWriter(new OutputStreamWriter(this.clientSocket.getOutputStream(), "UTF-8"));
	}
	
	@Override
	public void run() {
		try {
			while(true) {
				String message = this.in.readLine();
				handleMessageWithConnect(message.split(Protocol.DELIMITER));
			}
		} catch (IOException e) {
			//This means someone disconnected
		} catch (ProtocolViolatedException e) {
			this.server.print(e.getMessage());
		}
	}
	
	/**
	 * This method is always called over <code>handleMessage()</code>, because it will
	 * filter out the CONNECT type packet. If it is that type of packet, it will handle
	 * it. If it is not a CONNECT type packet, and the CONNECT packet was sent before,
	 * it will forward the data to <code>handleMessage()</code>, which will handle all
	 * other type of messages.
	 * @param data
	 * an array of all the information blocks of the packet.
	 * @throws ProtocolNotFollowedException 
	 * when the networking protocol is violated in any way.
	 */
	private void handleMessageWithConnect(String[] data) throws ProtocolViolatedException {
		String packetType = data[0];
		if(this.clientUsername != null && !packetType.equals(Protocol.Packets.CONNECT)) {
			handleMessage(data);
		} else if(clientUsername != null) {
			this.server.print("Client sent another connection packet?");
		} else {
			this.clientUsername = data[1];
			int extensionAmount = data.length - 2;
			this.extensions = new String[extensionAmount];
			for(int c = 0; c < extensionAmount; c++) {
				this.extensions[c] = data[c + 2];
			}
			String extensionString = "";
			for(int c = 0; c < RinggzServer.EXTENSIONS.length; c++) {
				extensionString = extensionString + Protocol.DELIMITER + RinggzServer.EXTENSIONS[c];
			}
			sendMessage(Packets.CONNECT + Protocol.DELIMITER + Protocol.ACCEPT + extensionString);
			this.server.print("New client [" + this.clientUsername + "] connected to the server.");
		}
	}
	
	/**
	 * Handles any other packets than the CONNECT packet. Notice packets like MOVE (which
	 * have to do with playing the game) do also go through this method, which it
	 * forwards to a <code>GameManager</code> if the client is currently in-game.
	 * @param data
	 * an array of all the information blocks of the packet.
	 * @throws ProtocolNotFollowedException 
	 * when the networking protocol is violated in any way.
	 */
	private void handleMessage(String[] data) throws ProtocolViolatedException {
		String packetType = data[0];
		switch (packetType) {
		
		case Packets.GAME_REQUEST:
			if(game == null) {
				try {
					int playerAmount = Integer.parseInt(data[1]);
					if(playerAmount < 2 || playerAmount > 4) {
						throw new ProtocolViolatedException("Data[1] is integer, but is out of range.");
					}
					if(data[2].equals(Protocol.HUMAN_PLAYER) || data[2].equals(Protocol.COMPUTER_PLAYER)) {
						this.playerType = data[2];
						if(data.length == 4) {
							this.game = this.server.getLobby(playerAmount, this.playerType, data[3]);
						} else if(data.length == 3) {
							this.game = this.server.getLobby(playerAmount, this.playerType);
						}
						if(this.game.addPlayer(this)) {
							sendMessage(Protocol.Packets.JOINED_LOBBY);
						} else {
							this.game = null;
						}
					} else {
						throw new ProtocolViolatedException("Data[2] is not a player type");
					}
				} catch(NumberFormatException e) {
					throw new ProtocolViolatedException("Data[1] is not an integer");
				} catch(ArrayIndexOutOfBoundsException e) {
					throw new ProtocolViolatedException("Too few arguments given for GAME_REQUEST from client.");
				}
			} else {
				throw new ProtocolViolatedException("Client requested game while already in a lobby.");
			}
			break;
		case Packets.PLAYER_STATUS:
			if(this.game != null) {
				if(data.length == 2) {
					setResponded(true);
					if(data[1].equals(Protocol.ACCEPT)) {
						setReady(true);
					} else {
						setReady(false);
					}
					synchronized (this.game) {
						this.game.notify();
					}
				} else {
					throw new ProtocolViolatedException("Too few arguments given for PLAYER_STATUS by client (GameManager.java).");
				}
			} else {
				throw new ProtocolViolatedException("Player gave ready status while not in a lobby.");
			}
			break;
		case Packets.MESSAGE:
			handleChatMessage(data);
			break;
			
		/*
		 * Packets below this point have to do with playing the game, and therefore are
		 * forwarded to a GameManager (IF the client is actually in a game, of course).
		 */
		case Packets.MOVE:
			if(this.game != null) {
				this.game.handleMessage(this, data);
			}
			break;
			
		default:
			break;
		}
	}
	
	private void handleChatMessage(String[] data) throws ProtocolViolatedException {
		String message;
		String messageType ;
		if(data.length >= 3 && data.length <= 4) {
			message = data[1];
			messageType = data[2];
			switch(messageType) {
			
			case Protocol.GLOBAL:
				this.server.broadcast(Protocol.Packets.MESSAGE + Protocol.DELIMITER + message + Protocol.DELIMITER + messageType + Protocol.DELIMITER + clientUsername);
				break;
			case Protocol.LOBBY:
				break;
			case Protocol.PRIVATE:
				if(data.length >= 4) {
					String receiver = data[3];
					ClientHandler handler = this.server.getClientHandlerFor(receiver);
					if(handler != null) {
						if(handler.clientHasExtensions(Extensions.EXTENSION_CHATTING)) {
							handler.sendMessage(Protocol.Packets.MESSAGE + Protocol.DELIMITER + message + Protocol.DELIMITER + messageType + Protocol.DELIMITER + clientUsername);
						}
					} else {
						throw new ProtocolViolatedException("Given receiver username does not exist or is not online.");
					}
				} else {
					throw new ProtocolViolatedException("Receiver was not given for a message of type PRIVATE.");
				}
				break;
			
			}
		} else {
			throw new ProtocolViolatedException("Wrong number of information blocks for MESSAGE packet.");
		}
	}
	
	/**
	 * Sends a given string to the inputstream of the client. If the writing to the
	 * client somehow fails, the thread of this <code>ClientHandler</code> is
	 * suspended.
	 * @param message
	 * The string message that will be sent to the client.
	 */
	public void sendMessage(String message) {
		try {
			this.out.write(message + "\n");
			this.out.flush();
		} catch (IOException e) {
			// connection was lost. Ergo: client disconnected.
			// TODO: let this end this Thread.
			this.server.print("Something went wrong writing to client.");
		}
	}
	
	public String getClientUsername() {
		return this.clientUsername;
	}
	
	public boolean clientHasExtensions(String extension) {
		if(this.extensions != null) {
			for(int c = 0; c < this.extensions.length; c++) {
				if(this.extensions[c].equals(extension)) {
					return true;
				}
			}
		}
		return false;
	}
	
	public String getPlayerType() {
		return this.playerType;
	}

	public boolean hasResponded() {
		return responded;
	}

	public void setResponded(boolean responded) {
		this.responded = responded;
	}

	public boolean isReady() {
		return ready;
	}

	public void setReady(boolean ready) {
		this.ready = ready;
	}
}