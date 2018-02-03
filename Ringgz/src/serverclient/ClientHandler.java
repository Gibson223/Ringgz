package serverclient;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.net.Socket;
import java.util.Arrays;

import controller.GameController;
import serverclient.Protocol.Extensions;
import serverclient.Protocol.Packets;

public class ClientHandler implements Runnable {
	private BufferedReader dis;
	private PrintWriter dos;
	private Server server;
	private final Socket clientSocket;
	public String username;
	private boolean ready; // == ready
	private boolean responded; // == responded
	public GameController linkedgame;

	public boolean getReady() {
		return this.ready;
	}

	public boolean getResponded() {
		return this.getResponded();
	}

	// Constructor
	public ClientHandler(Server server, Socket clientSocket) throws IOException {
		this.server = server;
		this.clientSocket = clientSocket;
		this.dis = new BufferedReader(new InputStreamReader(clientSocket.getInputStream(), "UTF-8"));
		this.dos = new PrintWriter(clientSocket.getOutputStream(), true);
		ready = false;
		responded = false;
	}

	@Override
	public void run() {
		try {
			while (true) {
				String message = this.dis.readLine();
				this.server.serverPrint(message);
				String[] splitmessage = message.split(Protocol.DELIMITER);
				this.packetHandler(splitmessage);
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		// todo splitter init message contains packettype, username

	}

	private void packetHandler(String[] fullpacket) throws IOException {
		String packet = fullpacket[0];
		if (packet == Packets.CONNECT) {
			this.server.serverPrint(fullpacket.toString());
			// dont understand why Connection already established so look for other data
			if (packet.equals(Packets.CONNECT) && this.username == null) {
				this.username = fullpacket[1];
//				if (fullpacket.length > 2) {
//					for (int i = 2; i < fullpacket.length;) {
//						if (fullpacket[i].equals(Extensions.EXTENSION_CHATTING)) {
//							this.dos.write((Packets.CONNECT + Protocol.DELIMITER
//									+ Protocol.ACCEPT /* + Protocol.DELIMITER + Extensions.EXTENSION_CHATTING */));
//							break;
//						}
//					}
//				} else {
					this.dos.write((Packets.CONNECT + Protocol.DELIMITER + Protocol.ACCEPT + Protocol.DELIMITER));
					this.server.serverPrint("connect packet received");
//				}
			}
		} else if (Packets.GAME_REQUEST.equals(packet)) {
			try {
				int preferredplayers = Integer.parseInt(fullpacket[1]);
				this.linkedgame = this.server.getGame(this, preferredplayers);
				if (this.linkedgame != null) {
					this.sendmessage(Protocol.Packets.JOINED_LOBBY);
				}
			} catch (NumberFormatException e) {
			} // TODO what todo??!?!??!?!
		} else if (packet == Packets.PLAYER_STATUS) {
			if (this.linkedgame != null) {
				if (fullpacket.length >= 2 && fullpacket[1].equals(Protocol.ACCEPT)) {
					this.responded = true;
					this.ready = true;
				} else {
					responded = false;
				}
				synchronized (this.linkedgame) {
					this.linkedgame.notify();
				}
			}
		}
		// else if (Packets.MOVE.equals(packet) ) {
		// if(this.linkedgame != null && this.linkedgame.started) {
		// String[] movedata = Arrays.copyOfRange(fullpacket, 1, fullpacket.length);
		// this.linkedgame.moveMade(this.username, movedata);
		// } else { this.server.serverPrint("client sending move package when not
		// playing a game...");}
		// }
		else {
			this.server.serverPrint("unknown packet type received at clienthandler of " + this.username);
		}
	}

	public void sendmessage(String message) throws IOException {
		this.dos.write(message);
		this.dos.println(message);
		this.dos.flush();
		this.server.serverPrint(message);
	}

}
