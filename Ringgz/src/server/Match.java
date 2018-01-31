package server;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import controller.Player;
import model.Board;
import serverclient.Protocol;
import serverclient.ProtocolException;
import serverclient.Protocol.Packets;

/**
 * The purpose of this class is to manage a certain game.
 */
public class Match implements Runnable {

	// List of players.
	private List<Player> players;

	// List of Client Assistants.
	private final List<Connection> Assistants;

	// The server the match will be played on.
	private final Server server;

	// The board the players play in.
	private Board board;

	// Returns if a lobby is currently in the middle of a game.
	private boolean gameOn;

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
		this.gameOn = false;
		this.Assistants = new ArrayList<>();
	}

	// Creates a lobby with a maximum of four players.
	public Match(Server server) {
		this(server, 4);
	}

	@Override
	public void run() {
		while (!this.gameOn) {
			try {
				waitForPlayers();
				mixPlayers();
				this.gameOn = start();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
	}

	public void handleMessage(Connection assistant, String[] data) throws ProtocolException {
		String packetType = data[0]; // First element of the data block represents the packet type
		switch (packetType) {
		default:
			throw new ProtocolException("There's something wrong with the protocol implementation");
		}
	}

	private synchronized void waitForPlayers() throws InterruptedException {
		while (getCurrentPlayers() < maxPlayers()) {
			wait();
		}
	}

	// Tries to start the game and returns whether it has been possible.
	// The synchronized block serves the purpose of being able to handle more than
	// one game in the same server without them interfering with one another
	private synchronized boolean start() throws InterruptedException {
		String usernames = "";
		for (Connection assistant : this.Assistants) {
			usernames += Protocol.DELIMITER + assistant.getUsername();
		}
		for (Connection assistant : this.Assistants) {
			assistant.sendPrompt(Packets.ALL_PLAYERS_CONNECTED + usernames);
		}
		long startingTime = System.currentTimeMillis();
		while (!allResponded()) {
			long presentTime = System.currentTimeMillis();
			if ((presentTime - startingTime) < STATUS_WAIT) {
				wait(STATUS_WAIT);
			}
		}
		if (!allAccepted()) {
			for (Connection assistant : this.Assistants) {
				if (!assistant.hasResponded() || !assistant.isReady()) {
					removePlayer(assistant);
				}
			}
			for (Connection assistant : this.Assistants) {
				assistant.sendPrompt(Packets.JOINED_LOBBY);
			}
			this.server
					.print("Couldn't start game because " + (maxPlayers() - getCurrentPlayers()) + " players refused.");
			return false;
		} else {
			for (Connection assistant : this.Assistants) {
				assistant.sendPrompt(Packets.GAME_STARTED);
			}
			this.server.print(" The game has started with " + getCurrentPlayers() + " players.");
			return true;
		}
	}

	// Returns whether all the players have answered a certain prompt.
	private boolean allResponded() {
		for (Connection assistant : this.Assistants) {
			if (!assistant.hasResponded()) {
				return false;
			}
		}
		return true;
	}

	// Returns whether all the players have accepted to start the game.
	private boolean allAccepted() {
		for (Connection assistant : this.Assistants) {
			if (!assistant.isReady()) {
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
		return this.Assistants;
	}

	// Returns whether the lobby is full or not.
	public boolean isFull() {
		return getCurrentPlayers() == this.maxPlayers;
	}

	// Shuffles the order of the players for a random starting order
	private void mixPlayers() {
		Collections.shuffle(this.Assistants);
	}

	// Adds a player to this lobby. Returns whether he/she could join.
	public synchronized boolean addPlayer(Connection assistant) {
		if (!this.gameOn && getCurrentPlayers() < this.maxPlayers
				&& (this.playerPreference == null || this.playerPreference.equals(assistant.getPlayerKind()))) {
			this.Assistants.add(assistant);
			notify();
			return true;
		} else {
			return false;
		}
	}

	// Removes a certain player.
	public void removePlayer(Connection assistant) {
		this.Assistants.remove(assistant);
	}

	// Returns the maximum amount of players.
	public int maxPlayers() {
		return this.maxPlayers;
	}

	// Returns the current amount of players in the lobby.
	public int getCurrentPlayers() {
		return this.Assistants.size();
	}
}