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
import view.*;

public class Server implements Runnable {
	public static final int PORT = 23197;
	private ServerSocket server;
	private List<GameController> games;
	private List<ClientHandler> clients;
	private BufferedReader dis;
	private BufferedWriter dos;
	private boolean online;

	public Server() throws IOException {
		this.server = new ServerSocket(PORT);
		this.games = new LinkedList<GameController>();
		this.clients = (new LinkedList<>());
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
		this.acceptPlayers();
	}

	public void acceptPlayers() {
		while (online) {
			try {
				// socket object to receive incoming client requests
				Socket clientSocket = server.accept();
				// obtaining input and out streams
				ClientHandler clienthandler = new ClientHandler(clientSocket);
				new Thread(clienthandler).start();
				this.addHandler(clienthandler);
				System.out.println("Assigned new thread for client" + clientSocket);
			} catch (IOException e) {
			}
		}
	}

	public void serverPrint(String s) {
		System.out.println(s);
	}

	public List<ClientHandler> getClients() {
		return clients;
	}

	public void addHandler(ClientHandler ch) {
		this.clients.add(ch);
	}

}
