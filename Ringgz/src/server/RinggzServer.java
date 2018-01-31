package server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

import serverclient.Protocol;
import serverclient.Protocol.Extensions;
import view.*;

public class RinggzServer implements Runnable {
	
	public static final int PORT = 23197;
	public static final String[] EXTENSIONS = new String[] {Extensions.EXTENSION_CHATTING};
	
	private List<GameManager> games;
	private List<ClientHandler> clientHandlers;
	private ServerSocket socket;
	private boolean running;
	
	public RinggzServer() throws IOException {
		this.games = new ArrayList<>();
		this.clientHandlers = new ArrayList<>();
		this.socket = new ServerSocket(PORT);
		this.running = true;
	}
	
	@Override
	public void run() {
		try {
			acceptClients();
			shutdown();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	private void acceptClients() throws IOException {
		while(running) {
			Socket client = socket.accept();
			ClientHandler handler = new ClientHandler(this, client);
			new Thread(handler).start();
			clientHandlers.add(handler);
		}
	}
	
	private void shutdown() throws IOException {
		socket.close();
	}
	
	public void print(String message) {
		System.out.println(message);
	}
	
	/**
	 * Sends a message to all currently connected clients.
	 * @param message
	 * The message that will be sent.
	 */
	public void broadcast(String message) {
		for(ClientHandler handler : clientHandlers) {
			handler.sendMessage(message);
		}
	}
	
	public void sendMessageTo(String message, String receiver) {
		ClientHandler handler = getClientHandlerFor(receiver);
		if(handler != null) {
			handler.sendMessage(message);
		}
	}
	
	public ClientHandler getClientHandlerFor(String username) {
		for(ClientHandler handler : clientHandlers) {
			if(handler.getClientUsername().equals(username)) {
				return handler;
			}
		}
		return null;
	}
	
	/**
	 * Returns a game lobby for the given player- amount and type.
	 * @param playerAmount
	 * The preferred amount of players in the game.
	 * @param playerType
	 * The type of the player that wants to join a lobby.
	 * @return
	 * Returns an existing <code>GameManager</code> that is not ingame with the player's
	 * preferences. Returns a <code>new GameManager</code> if one with the player's
	 * preferences does not exist.
	 */
	public GameManager getLobby(int playerAmount, String playerType) {
		return getLobby(playerAmount, playerType, null);
	}
	
	/**
	 * Returns a game lobby for the given player- amount and type.
	 * @param playerAmount
	 * The preferred amount of players in the game.
	 * @param playerType
	 * The type of the player that wants to join a lobby.
	 * @param opponentType
	 * The preferred type of opponent the player wants to play with. If this argument is
	 * <code>null</code>, or does not represent a player type from the given protocol code,
	 * no preference is assumed.
	 * @return
	 * Returns an existing <code>GameManager</code> that is not ingame with the player's
	 * preferences. Returns a <code>new GameManager</code> if one with the player's
	 * preferences does not exist.
	 */
	public GameManager getLobby(int playerAmount, String playerType, String opponentType) {
		if(opponentType != null && !opponentType.equals(Protocol.HUMAN_PLAYER) && !opponentType.equals(Protocol.COMPUTER_PLAYER)) {
			opponentType = null;
		}
		for(GameManager game : games) {
			if(!game.isFull() && game.getMaxPlayers() == playerAmount && (game.getPlayerType() == null || game.getPlayerType().equals(playerType))) {
				if(opponentType == null) {
					return game;
				} else {
					List<ClientHandler> gamePlayers = game.getPlayers();
					boolean valid = true;
					for(int c = 0; c < gamePlayers.size(); c++) {
						if(!gamePlayers.get(c).getPlayerType().equals(opponentType)) {
							valid = false;
							break;
						}
					}
					if(valid) {
						return game;
					}
				}
			}
		}
		GameManager game = new GameManager(this, playerAmount);
		new Thread(game).start();
		this.games.add(game);
		return game;
	}
	
	/**
	 * Starts the <code>RinggzServer</code>
	 * @param args
	 * Unused.
	 */
	public static void main(String[] args) {
		try {
			new Thread(new RinggzServer()).start();
			System.out.println("The server has been started.");
			TUI tui = new TUI();
			tui.run();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}