package server;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import controller.NetworkPlayer;
import controller.Player;
import model.Base;
import model.Board;
import model.Ring;
import model.StartBase;
import net.Protocol;
import net.Protocol.Packets;
import net.ProtocolViolatedException;

/**
 * This class is supposed to manage one specific game, it is initialized with connections
 * to all the players and this manager will take care of starting the game and performing
 * any game logic.
 */
public class GameManager implements Runnable {
	
	private static final long STATUS_WAIT = 10000;
	
	private final RinggzServer server;
	
	/**
	 * List  of <code>ClientHandler</code>s. These handlers are in charge of the network
	 * communication with the players. Anything that is supposed to be handled by the
	 * <code>GameManager</code> will be forwarded from these handlers.
	 */
	private final List<ClientHandler> clientHandlers;
	
	/**
	 * List of players. The indeces in this list correspond with the indices of the 
	 * handlers in the <code>clientHandlers</code> list.
	 */
	private List<Player> players;
	
	/**
	 * The <code>Board</code> that the players in this lobby interact with.
	 */
	private Board board;
	
	/**
	 * Boolean indicating whether this lobby is playing a game. If this boolean is
	 * <code>false</code>, the lobby is still either waiting on new players or is currently
	 * trying to start the game.
	 */
	private boolean ingame;
	
	/*
	 * Lobby preferences by lobby creator.
	 */
	
	/**
	 * Amount of players that the lobby will wait for before it starts the game.
	 */
	private final int maxPlayers;
	
	/**
	 * Preferred player type for the lobby of the lobby creator. If this is <code>null</code>,
	 * the lobby creator had no preference while creating the lobby.
	 */
	public String playerTypePreference;
	
	/**
	 * Creates a <code>GameManager</code> (lobby) with a given maximum amount of
	 * players.
	 * @param maxPlayers
	 * the maximum amount of players.
	 */
	public GameManager(RinggzServer server, int maxPlayers) {
		this.server = server;
		this.maxPlayers = maxPlayers;
		this.clientHandlers = new ArrayList<>();
		this.ingame = false;
	}
	
	/**
	 * Creates a <code>GameManager</code> with a maximum of four players.
	 */
	public GameManager(RinggzServer server) {
		this(server, 4);
	}

	@Override
	public void run() {
		while(!this.ingame) {
			try {
				waitForPlayers();
				shufflePlayers();
				this.ingame = startGame();
			} catch (InterruptedException e) {
				// TODO: lobby should be suspended.
			}
		}
		preperationPhase();
		playingPhase();
		endingPhase();
	}
	
	public void handleMessage(ClientHandler handler, String[] data) throws ProtocolViolatedException {
		String packetType = data[0];
		switch(packetType) {
		
		// handle MOVE packets
		
		default:
			throw new ProtocolViolatedException("Unhandled packet in GameManager.java: " + packetType);
		}
	}
	
	private synchronized void waitForPlayers() throws InterruptedException {
		while(getCurrentPlayers() < getMaxPlayers()) {
			wait();
		}
	}
	
	/**
	 * This shuffles the <code>clientHandlers</code> list. The order of this list will be
	 * used in the game.
	 */
	private void shufflePlayers() {
		Collections.shuffle(this.clientHandlers);
	}
	
	/**
	 * Attempts to start the game and returns whether this attempt has been successful.
	 * @return
	 * <code>true</code> if the game has started, <code>false</code> otherwise.
	 * @throws InterruptedException 
	 */
	private synchronized boolean startGame() throws InterruptedException {
		String usernames = "";
		for(ClientHandler handler : this.clientHandlers) {
			usernames = usernames + Protocol.DELIMITER + handler.getClientUsername();
		}
		for(ClientHandler handler : this.clientHandlers) {
			handler.sendMessage(Packets.ALL_PLAYERS_CONNECTED + usernames);
		}
		long start = System.currentTimeMillis();
		while(!allPlayersResponded()) {
			long current = System.currentTimeMillis();
			if(current - start < STATUS_WAIT) {
				wait(STATUS_WAIT);
			}
		}
		if(!allPlayersAccepted()) {
			for(ClientHandler handler : this.clientHandlers) {
				if(!handler.hasResponded() || !handler.isReady()) {
					removePlayer(handler);
				}
			}
			for(ClientHandler handler : this.clientHandlers) {
				handler.sendMessage(Packets.JOINED_LOBBY);
			}
			this.server.print("Starting game failed: " + (getMaxPlayers() - getCurrentPlayers()) + " players refused.");
			return false;
		} else {
			for(ClientHandler handler : this.clientHandlers) {
				handler.sendMessage(Packets.GAME_STARTED);
			}
			this.server.print("Started a game with " + getCurrentPlayers() + " players.");
			return true;
		}
	}
	
	private boolean allPlayersResponded() {
		for(ClientHandler handler : this.clientHandlers) {
			if(!handler.hasResponded()) {
				return false;
			}
		}
		return true;
	}
	
	private boolean allPlayersAccepted() {
		for(ClientHandler handler : this.clientHandlers) {
			if(!handler.isReady()) {
				return false;
			}
		}
		return true;
	}
	
	/**
	 * This method prepares the server-side model for the game: it distributes colors and
	 * pieces amongst the players.
	 */
	private void preperationPhase() {
		this.players = new ArrayList<>();
		for(int c = 0; c < this.clientHandlers.size(); c++) {
			this.players.add(new NetworkPlayer());
		}
		if(this.players.size() == 2) {
			handPieces2Players();
		} else if(this.players.size() == 3) {
			handPieces3Players();
		} else {
			handPieces4Players();
		}
		this.players.get(0).givePiece(new StartBase());
	}
	
	private void handPieces2Players() {
		for(int p = 0; p < 2; p++) {
			Player player = this.players.get(p);
			player.setPrimaryColor(2 * p);
			player.setSecondaryColor(2 * p + 1);
			for(int color = 0; color < 2; color++) {
				for(int c = 0; c < 3; c++) {
					player.givePiece(new Base(2 * p + color));
					player.givePiece(new Ring(0, 2 * p + color));
					player.givePiece(new Ring(1, 2 * p + color));
					player.givePiece(new Ring(2, 2 * p + color));
					player.givePiece(new Ring(3, 2 * p + color));
				}
			}
		}
	}

	private void handPieces3Players() {
		for(int p = 0; p < 3; p++) {
			Player player = this.players.get(p);
			player.setPrimaryColor(p);
			player.setSecondaryColor(4);
			for(int c = 0; c < 3; c++) {
				player.givePiece(new Base(p));
				player.givePiece(new Ring(0, p));
				player.givePiece(new Ring(1, p));
				player.givePiece(new Ring(2, p));
				player.givePiece(new Ring(3, p));
			}
			player.givePiece(new Base(4));
			player.givePiece(new Ring(0, 4));
			player.givePiece(new Ring(1, 4));
			player.givePiece(new Ring(2, 4));
			player.givePiece(new Ring(3, 4));
		}
	}

	private void handPieces4Players() {
		for(int p = 0; p < 4; p++) {
			Player player = this.players.get(p);
			player.setPrimaryColor(p);
			for(int c = 0; c < 3; c++) {
				player.givePiece(new Base(p));
				player.givePiece(new Ring(0, p));
				player.givePiece(new Ring(1, p));
				player.givePiece(new Ring(2, p));
				player.givePiece(new Ring(3, p));
			}
		}
	}

	/**
	 * This method performs all game logic while playing the game. It checks if the player
	 * that currently has the turn can move, asks it to make a move if it can and forwards
	 * this information to all other players. It will loop this sequence until the game is
	 * done. When this happens, this method will terminate.
	 */
	private void playingPhase() {
		// TODO Auto-generated method stub
	}

	private void endingPhase() {
		// TODO Auto-generated method stub
	}
	
	/**
	 * Adds a player to this lobby. Returns if the joining was successful.
	 * @param handler
	 * The handler of the client that wants to join this lobby.
	 * @return
	 * <code>true</code> of joining the client was successful, <code>false</code>
	 * otherwise.
	 */
	public synchronized boolean addPlayer(ClientHandler handler) {
		if(!this.ingame && getCurrentPlayers() < this.maxPlayers && (this.playerTypePreference == null  || this.playerTypePreference.equals(handler.getPlayerType()))) {
			this.clientHandlers.add(handler);
			notify();
			return true;
		} else {
			return false;
		}
	}
	
	public void removePlayer(ClientHandler handler) {
		this.clientHandlers.remove(handler);
	}
	
	public int getMaxPlayers() {
		return this.maxPlayers;
	}
	
	public int getCurrentPlayers() {
		return this.clientHandlers.size();
	}
	
	public String getPlayerType() {
		return this.playerTypePreference;
	}
	
	public List<ClientHandler> getPlayers() {
		return this.clientHandlers;
	}
	
	public boolean isFull() {
		return getCurrentPlayers() == this.maxPlayers;
	}
}