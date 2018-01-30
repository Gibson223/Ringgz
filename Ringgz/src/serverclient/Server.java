package serverclient;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.LinkedList;
import java.util.List;

import controller.GameController;
import model.*;
import net.Protocol;
import view.*;

public class Server implements Runnable {
	public static final int PORT = 23197;
	private ServerSocket server;
	private List<GameController> games;
	private List<ClientHandler> clients;
	private BufferedReader dis;
	private BufferedWriter dos;
	private boolean online;
	private String playerType;//TODO necessary to keep in acount???
	public final int WAIT = 10000;

	public Server() throws IOException {
		this.server = new ServerSocket(PORT);
		this.games = new LinkedList<GameController>();
		this.clients = new LinkedList<>();
		online = true;
	}

	public static void main(String[] args) throws IOException {
		System.out.println("starting server");
		Server server = new Server();
		Thread s = new Thread(server);
		s.start();
	}

	@Override
	public void run() {
		this.acceptClientSockets();
		try {
			this.shutDown();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public void acceptClientSockets() {
		while (online) {
			try {
				Socket clientSocket = server.accept();
				ClientHandler clienthandler = new ClientHandler(this,clientSocket);
				new Thread(clienthandler).start();
				this.addHandler(clienthandler);
				System.out.println("Assigned new thread for client" + clientSocket);
			} catch (IOException e) {
			}
		}
	}
	public GameController getGame(ClientHandler ch, int preferredplayers) {
		for (GameController gc: this.games) {
			if (gc.players.size() < gc.maxplayers && gc.addClient(ch)) {
				return gc;
			}
		}
		GameController newgame = new GameController(this, preferredplayers);
		newgame.addClient(ch);
		return newgame;
	}
	

	public void serverPrint(String s) {
		System.out.println(s);
	}

	public List<ClientHandler> getClients() {
		return clients;
	}

	private void addHandler(ClientHandler ch) {
		this.clients.add(ch);
	}
	private void removeHandler(ClientHandler ch) {
		this.clients.remove(ch);
	}
	//requires packet matches extension chatting
	public void serverMessage(String message) {
		for(ClientHandler clienthandler: this.getClients()) {
		clienthandler.sendmessage(message);
		}
	}
	private void shutDown() throws IOException {
		this.dis.close();
		this.dos.close();
		this.server.close();
	}
}
