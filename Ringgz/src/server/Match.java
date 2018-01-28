package server;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import controller.Player;
import model.Board;
import net.Protocol;
import net.Protocol.Packets;
import net.ProtocolException;

/**
 * The purpose of this class is to manage a certain game.
 */
public class Match implements Runnable {

	// List of players.
	private List<Player> players;

	// List of Client Handlers.
	private final List<Connection> clientHandlers;

	private final Server server;

	// The board the players play in.
	private Board board;

	// Returns if a lobby is currently in the middle of a game.
	private boolean ingame;

	// Amount of players that will be allowed in a game (chosen by player).
	private final int maxPlayers;

	// String that indicates what kind of player a player wants to play against.
	public String playerPreference;
	
	// This will be the wait time (in ms) for the confirmation when players join a
	// server.
	private static final long STATUS_WAIT = 30000;

	/**
	 * Creates a lobby with a max amount of players.
	 * 
	 * @param maxPlayers
	 *            maximum amount of players.
	 */
	public Match(Server server, int maxPlayers) {
		this.server = server;
		this.maxPlayers = maxPlayers;
		this.ingame = false;
		this.clientHandlers = new ArrayList<>();
	}

	// Creates a lobby with a maximum of four players.
	public Match(Server server) {
		this(server, 4);
	}

	@Override
	public void run() {
		while (!this.ingame) {
			try {
				waitForPlayers();
				shufflePlayers();
				this.ingame = startGame();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
	}

	public void handleMessage(Connection handler, String[] data) throws ProtocolException {
		String packetType = data[0];
		switch (packetType) {
		default:
			throw new ProtocolException("Unhandled packet in GameManager.java: " + packetType);
		}
	}

	private synchronized void waitForPlayers() throws InterruptedException {
		while (getCurrentPlayers() < maxPlayers()) {
			wait();
		}
	}

	// Tries to start the game and returns whether it has been possible.
	private synchronized boolean startGame() throws InterruptedException {
		String usernames = "";
		for (Connection handler : this.clientHandlers) {
			usernames += Protocol.DELIMITER + handler.getUsername();
		}
		for (Connection handler : this.clientHandlers) {
			handler.sendMessage(Packets.ALL_PLAYERS_CONNECTED + usernames);
		}
		long start = System.currentTimeMillis();
		while (!allResponded()) {
			long current = System.currentTimeMillis();
			if (current - start < STATUS_WAIT) {
				wait(STATUS_WAIT);
			}
		}
		if (!allAccepted()) {
			for (Connection handler : this.clientHandlers) {
				if (!handler.hasResponded() || !handler.isReady()) {
					removePlayer(handler);
				}
			}
			for (Connection handler : this.clientHandlers) {
				handler.sendMessage(Packets.JOINED_LOBBY);
			}
			this.server.print(
					"Couldn't start game because " + (maxPlayers() - getCurrentPlayers()) + " players refused.");
			return false;
		} else {
			for (Connection handler : this.clientHandlers) {
				handler.sendMessage(Packets.GAME_STARTED);
			}
			this.server.print(" The game has started with " + getCurrentPlayers() + " players.");
			return true;
		}
	}

	// Returns whether all the players have answered a certain prompt.
	private boolean allResponded() {
		for (Connection handler : this.clientHandlers) {
			if (!handler.hasResponded()) {
				return false;
			}
		}
		return true;
	}

	// Returns whether all the players have accepted to start the game.
	private boolean allAccepted() {
		for (Connection handler : this.clientHandlers) {
			if (!handler.isReady()) {
				return false;
			}
		}
		return true;
	}

	// Returns whether a player is human or a computer.
	public String getPlayerType() {
		return this.playerPreference;
	}

	// Returns a list with all the players.
	public List<Connection> getPlayers() {
		return this.clientHandlers;
	}

	// Returns whether the lobby is full or not.
	public boolean isFull() {
		return getCurrentPlayers() == this.maxPlayers;
	}

	// Shuffles the order of the players for a random starting order
	private void shufflePlayers() {
		Collections.shuffle(this.clientHandlers);
	}

	// Adds a player to this lobby. Returns whether he/she could join.
	public synchronized boolean addPlayer(Connection handler) {
		if (!this.ingame && getCurrentPlayers() < this.maxPlayers
				&& (this.playerPreference == null || this.playerPreference.equals(handler.getPlayerKind()))) {
			this.clientHandlers.add(handler);
			notify();
			return true;
		} else {
			return false;
		}
	}

	// Removes a certain player.
	public void removePlayer(Connection handler) {
		this.clientHandlers.remove(handler);
	}

	// Returns the maximum amount of players.
	public int maxPlayers() {
		return this.maxPlayers;
	}

	// Returns the current amount of players in the lobby.
	public int getCurrentPlayers() {
		return this.clientHandlers.size();
	}
}