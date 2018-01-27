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

/*
 * The job of this class is to keep a certain client's connection with the server
 */
public class ClientHandler implements Runnable {

	private final BufferedReader in;
	private final BufferedWriter out;
	private final Server server;
	private final Socket clientSocket;
	private String clientUsername;
	private String[] extensions;

	/**
	 * Game the client this handler refers to is in.
	 */
	private GameManager game;

	/**
	 * The player type of the client of this handler.
	 */
	private String playerType;

	public ClientHandler(Server server, Socket clientSocket) throws IOException {
		this.server = server;
		this.clientSocket = clientSocket;
		this.in = new BufferedReader(new InputStreamReader(this.clientSocket.getInputStream(), "UTF-8"));
		this.out = new BufferedWriter(new OutputStreamWriter(this.clientSocket.getOutputStream(), "UTF-8"));
	}

	@Override
	public void run() {
		try {
			while (true) {
				String message = this.in.readLine();
				handleMessageWithConnect(message.split(Protocol.DELIMITER));
			}
		} catch (IOException e) {
			// This means someone disconnected
		} catch (ProtocolViolatedException e) {
			this.server.print(e.getMessage());
		}
	}

	/**
	 * This method handles the CONNECT packet.
	 * 
	 * @param data
	 *            an array of all the information blocks of the packet.
	 * @throws ProtocolNotFollowedException
	 *             is thrown if the protocol is violated in any way.
	 */
	private void handleMessageWithConnect(String[] data) throws ProtocolViolatedException {
		String packetType = data[0];
		if (this.clientUsername != null && !packetType.equals(Protocol.Packets.CONNECT)) {
			handleMessage(data);
		} else if (clientUsername != null) {
			this.server.print("Client sent another connection packet?");
		} else {
			this.clientUsername = data[1];
			int extensionAmount = data.length - 2;
			this.extensions = new String[extensionAmount];
			for (int c = 0; c < extensionAmount; c++) {
				this.extensions[c] = data[c + 2];
			}
			// String extensionString = "";
			// for (int c = 0; c < Server.EXTENSIONS.length; c++) {
			// extensionString += Protocol.DELIMITER + Server.EXTENSIONS[c];
			// }
			sendMessage(Packets.CONNECT + Protocol.DELIMITER + Protocol.ACCEPT); // + extensionString
			this.server.print("[" + this.clientUsername + "] has connected to the server.");
		}
	}

	private boolean ready;
	private boolean responded;

	/**
	 * Handles every packet except for the CONNECT packet (see method above).
	 * 
	 * @param data
	 *            an array of all the information blocks of the packet.
	 * @throws ProtocolNotFollowedException
	 *             is thrown if the protocol is violated in any way.
	 */
	private void handleMessage(String[] data) throws ProtocolViolatedException {
		String packetType = data[0];
		switch (packetType) {

		case Packets.GAME_REQUEST:
			if (game == null) {
				try {
					int playerAmount = Integer.parseInt(data[1]);
					if (playerAmount < 2 || playerAmount > 4) {
						throw new ProtocolViolatedException("Data[1] isn't a valid integer.");
					}
					if (data[2].equals(Protocol.HUMAN_PLAYER) || data[2].equals(Protocol.COMPUTER_PLAYER)) {
						this.playerType = data[2];
						if (data.length == 4) {
							this.game = this.server.getLobby(playerAmount, this.playerType, data[3]);
						} else if (data.length == 3) {
							this.game = this.server.getLobby(playerAmount, this.playerType);
						}
						if (this.game.addPlayer(this)) {
							sendMessage(Protocol.Packets.JOINED_LOBBY);
						} else {
							this.game = null;
						}
					} else {
						throw new ProtocolViolatedException("Data[2] is not a valid player type");
					}
				} catch (NumberFormatException e) {
					throw new ProtocolViolatedException("Data[1] is not an integer");
				} catch (ArrayIndexOutOfBoundsException e) {
					throw new ProtocolViolatedException("Too few arguments given for GAME_REQUEST from client.");
				}
			} else {
				throw new ProtocolViolatedException("Client requested game while already in a lobby.");
			}
			break;
		case Packets.PLAYER_STATUS:
			if (this.game != null) {
				if (data.length == 2) {
					setResponded(true);
					if (data[1].equals(Protocol.ACCEPT)) {
						setReady(true);
					} else {
						setReady(false);
					}
					synchronized (this.game) {
						this.game.notify();
					}
				} else {
					throw new ProtocolViolatedException("Too few arguments given for PLAYER_STATUS by client.");
				}
			} else {
				throw new ProtocolViolatedException("Cannot give ready status while you aren't in a lobby.");
			}
			break;

		case Packets.MOVE:
			if (this.game != null) {
				this.game.handleMessage(this, data);
			}
			break;

		default:
			break;
		}
	}

	/**
	 * Sends a certain message to the client.
	 * 
	 * @param message
	 *            The message that will be sent.
	 */
	public void sendMessage(String message) {
		try {
			this.out.write(message + "\n");
			this.out.flush();
		} catch (IOException e) {
			this.server.print("There was an error writing to client.");
		}
	}

	public String getPlayerType() {
		return this.playerType;
	}

	public String getClientUsername() {
		return this.clientUsername;
	}

	public boolean clientHasExtensions(String extension) {
		if (this.extensions != null) {
			for (int c = 0; c < this.extensions.length; c++) {
				if (this.extensions[c].equals(extension)) {
					return true;
				}
			}
		}
		return false;
	}

	public boolean isReady() {
		return ready;
	}

	public boolean hasResponded() {
		return responded;
	}

	public void setResponded(boolean responded) {
		this.responded = responded;
	}

	public void setReady(boolean ready) {
		this.ready = ready;
	}
}