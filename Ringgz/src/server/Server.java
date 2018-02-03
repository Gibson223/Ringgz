package server;

import java.io.IOException;
import java.net.BindException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import serverclient.Protocol;

public class Server implements Runnable {

	public static int PORT = 23197;
	private List<Match> games;
	private List<Connection> Assistants;
	private ServerSocket socket;
	private boolean running;

	@Override
	public void run() {
		try {
			acceptClients();
			shutdown();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public Server() throws IOException {
		this.games = new ArrayList<>();
		this.Assistants = new ArrayList<>();
		this.socket = new ServerSocket(PORT);
		this.running = true;
	}

	private void acceptClients() throws IOException {
		while (running) {
			Socket client = socket.accept();
			Connection assistant = new Connection(this, client);
			new Thread(assistant).start();
			Assistants.add(assistant);
		}
	}

	// Shuts down the socket.
	private void shutdown() throws IOException {
		socket.close();
	}

	// Shortcut for sysout print.
	public void print(String message) {
		System.out.println(message);
	}

	// Sends a message to all users.
	public void sendAll(String message) {
		for (Connection assistant : Assistants) {
			assistant.sendPrompt(message);
		}
	}

	// Sends a message to a certain user.
	public void sendMessageTo(String message, String receiver) {
		Connection assistant = getClientassistantFor(receiver);
		if (assistant != null) {
			assistant.sendPrompt(message);
		}
	}

	// Returns the Client assistant of a certain user.
	public Connection getClientassistantFor(String username) {
		for (Connection assistant : Assistants) {
			if (assistant.getUsername().equals(username)) {
				return assistant;
			}
		}
		return null;
	}

	// Returns a game lobby for a certain player amount and type.
	public Match getLobby(int playerAmount, String playerType) {
		return getLobby(playerAmount, playerType, null);
	}

	// Creates a game lobby for a certain player amount and type.
	public Match getLobby(int playerAmount, String playerType, String opponentType) {
		if (opponentType != null && !opponentType.equals(Protocol.HUMAN_PLAYER)
				&& !opponentType.equals(Protocol.COMPUTER_PLAYER)) {
			opponentType = null;
		}
		for (Match game : games) {
			if (!game.isFull() && game.maxPlayers() == playerAmount
					&& (game.getPlayerType() == null || game.getPlayerType().equals(playerType))) {
				if (opponentType == null) {
					return game;
				} else {
					List<Connection> gamePlayers = game.getPlayers();
					boolean valid = true;
					for (int c = 0; c < gamePlayers.size(); c++) {
						if (!gamePlayers.get(c).getPlayerKind().equals(opponentType)) {
							valid = false;
							break;
						}
					}
					if (valid) {
						return game;
					}
				}
			}
		}
		Match game = new Match(this, playerAmount);
		new Thread(game).start();
		this.games.add(game);
		return game;
	}

	// Starts the Server
	public static void main(String[] args) {
		try {
			if (args.length > 0) {
				PORT = Integer.parseInt(args[0]);
			}
			new Thread(new Server()).start();
			System.out.println("The server has been started.");
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}