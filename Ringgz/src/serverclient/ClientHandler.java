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

import controller.GameController;
import net.Protocol;
import net.ProtocolViolatedException;
import net.Protocol.Extensions;
import net.Protocol.Packets;

public class ClientHandler implements Runnable{
	private BufferedReader dis;
	private PrintWriter dos;
	private Server server;
    private final Socket clientSocket;
    public  String username;
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
    public ClientHandler(Server server,Socket clientSocket) throws IOException 
    {
    	this.server = server;
        this.clientSocket = clientSocket;
        this.dis = new BufferedReader(new InputStreamReader(clientSocket.getInputStream(), "UTF-8"));
		this.dos = new PrintWriter(clientSocket.getOutputStream(), true);
		ready = false;
		responded = false;
    }
	@Override
	public void run(){
		try {
			while(true) {
<<<<<<< Upstream, based on origin/master
				String initmessage = this.dis.readLine();
				if (initmessage != null) {
					server.serverPrint(initmessage);
				}
=======
			String message = this.dis.readLine();
			this.packetHandler(message.split(Protocol.DELIMITER));
>>>>>>> eb5b220 did my best but i just got to go to bed.
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		//todo splitter init message contains packettype, username
		
	}
	private void packetHandler(String[] fullpacket) {
		String packet = fullpacket[0];
		if (packet == Packets.CONNECT) {
			//dont understand why Connection already established so look for other data
			if (packet.equals(Packets.CONNECT) && this.username == null) {
				this.username = fullpacket[1];
				if (fullpacket.length > 2) {
					for (int i = 2; i < fullpacket.length;) {
						if (fullpacket[i].equals(Extensions.EXTENSION_CHATTING)) {
							this.dos.println(Packets.CONNECT + Protocol.DELIMITER + 
									Protocol.ACCEPT /*+ Protocol.DELIMITER + Extensions.EXTENSION_CHATTING*/);
							break;
						}
					}
				}
				else {this.dos.println(Packets.CONNECT + Protocol.DELIMITER + Protocol.ACCEPT + Protocol.DELIMITER);}
			}
		}
		if (Packets.GAME_REQUEST.equals(packet)){
			try {
			int preferredplayers = Integer.parseInt( fullpacket[1]); 
			this.linkedgame = this.server.getGame(this, preferredplayers);
			if (this.linkedgame != null) {
				this.sendmessage(Protocol.Packets.JOINED_LOBBY);
			}
		}catch(NumberFormatException e) {	
		}//TODO what todo??!?!??!?!
		}
		else if (packet == Packets.PLAYER_STATUS) {
			if(this.linkedgame != null) {
				if(fullpacket.length >= 2 && fullpacket[1].equals(Protocol.ACCEPT)) {
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
		else if (Packets.MOVE.equals(packet) ) {
		if(this.linkedgame != null && this.linkedgame.started) {
			this.game.handleMessage(this, data);
		}
		}
	}
	public void sendmessage(String message) {
		this.dos.write(message);
		this.dos.flush();
	}
	
}
