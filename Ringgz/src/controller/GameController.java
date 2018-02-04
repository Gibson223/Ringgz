package controller;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import model.Board;
import model.Color;
import model.Field;
import model.Ring;
import model.RingList;
import model.Tier;
import serverclient.ClientHandler;
import serverclient.Protocol;
import serverclient.Server;
import serverclient.Protocol.Packets;
import view.TUI;

public class GameController implements Runnable {
	public List<Player> players = new ArrayList<Player>();
	public Board board;
	public TUI tui;
	public RingList ringlist;
	public int maxplayers;
	public List<ClientHandler> clients;
	private Server server;
	public boolean started;
	public final int ALLOWEDDELAY = 20000;
	int wonG = 0;
	int wonB = 0;
	int wonY = 0;
	int wonR = 0;
	private HashMap<Player, Integer> wonFields;

	public GameController(Server server, int maxplayers) {
		this.server = server;
		this.maxplayers = maxplayers;

	}

	public void run() {
		while (!this.started) { // TODO: clean way to stop this loop when server shuts down.
			this.startgame();
		}
	}
	public GameController(Player s0, Player s1, Player s2) {
		this(s0 ,s1 ,s2 ,null);
	}
	public GameController(Player s0, Player s1) {
		this(s0 ,s1 ,null ,null);
	}
	public GameController(Player s0, Player s1, Player s2, Player s3) {
		List<Object> playerlist = new ArrayList<>();
		List<ClientHandler> clients = new ArrayList<>();
		playerlist.add(s0);
		playerlist.add(s1);
		playerlist.add(s2);
		playerlist.add(s3);
		playerlist.stream().filter(a -> a != null).forEach(a -> players.add((Player) a));
		this.run();
	}

	private synchronized boolean startGame() throws InterruptedException, IOException {
		Collections.shuffle(clients);
		String usernames = "";
		for (ClientHandler client : this.clients) {
			usernames = usernames + Protocol.DELIMITER + client.username;
		}
		for (ClientHandler client : this.clients) {
			client.sendmessage(Packets.ALL_PLAYERS_CONNECTED + usernames);
		}
		long start = System.currentTimeMillis();
		while (!this.clients.stream().allMatch(a -> a.getResponded() == true)) {
			long current = System.currentTimeMillis();
			if (current - start < ALLOWEDDELAY) {
				wait();
			}
		}
		if (!allready()) {
			for (ClientHandler client : this.clients) {
				if (!client.getResponded() || !client.getReady()) {
					removeClient(client);
				}
			}
			for (ClientHandler client : this.clients) {
				client.sendmessage(Packets.JOINED_LOBBY);
			}
			return false;
		} else {
			for (ClientHandler client : this.clients) {
				client.sendmessage((Packets.GAME_STARTED));
			}
			return true;
		}
	}

	private boolean allready() {
		for (ClientHandler handler : this.clients) {
			if (!handler.getResponded() || !handler.getReady()) {
				return false;
			}
		}
		return true;
	}

	public synchronized boolean addPlayer(ClientHandler handler) {
		if (!this.started && this.clients.size() < this.maxplayers) {
			this.clients.add(handler);
			notify();
			return true;
		} else {
			return false;
		}
	}

	public void startgame() {
		board = new Board();
		ringlist = new RingList();
		// tui = new TUI();
		// for (Field field : board.fields) {
		// field.addObserver(tui);
		// }
		// tui.view();
		this.playerSetter();
		this.ringdivider();
		this.play();

	}

	public void playerSetter() {
		if (this.players.size() == 2) {
			players.get(0).setPrimary(Color.RED);
			players.get(0).setSecondary(Color.YELLOW);
			players.get(1).setPrimary(Color.GREEN);
			players.get(1).setSecondary(Color.BLUE);
		}
		if (this.players.size() == 3) {
			players.get(0).setPrimary(Color.RED);
			players.get(1).setPrimary(Color.YELLOW);
			players.get(2).setPrimary(Color.GREEN);
			players.get(0).setSecondary(Color.BLUE);
			players.get(1).setSecondary(Color.BLUE);
			players.get(2).setSecondary(Color.BLUE);
		}
		if (this.players.size() == 4) {
			players.get(0).setPrimary(Color.RED);
			players.get(1).setPrimary(Color.YELLOW);
			players.get(2).setPrimary(Color.GREEN);
			players.get(3).setPrimary(Color.BLUE);
		}
	}

	public void ringdivider() {
		if (this.players.size() == 2) {
			RingList ringlistpart1 = new RingList(new ArrayList<Ring>(ringlist.availableRings.subList(0, 30)));
			RingList ringlistpart2 = new RingList(new ArrayList<Ring>(ringlist.availableRings.subList(30, 60)));
			players.get(0).setRingList(ringlistpart1);
			players.get(1).setRingList(ringlistpart2);
		}
		if (this.players.size() == 3) {
			RingList ringlistpart1 = new RingList(new ArrayList<Ring>(ringlist.availableRings.subList(0, 15)));
			RingList ringlistpart2 = new RingList(new ArrayList<Ring>(ringlist.availableRings.subList(15, 30)));
			RingList ringlistpart3 = new RingList(new ArrayList<Ring>(ringlist.availableRings.subList(30, 45)));
			ringlistpart1.availableRings.addAll(new ArrayList<Ring>(ringlist.availableRings.subList(45, 50)));
			ringlistpart2.availableRings.addAll(new ArrayList<Ring>(ringlist.availableRings.subList(50, 55)));
			ringlistpart3.availableRings.addAll(new ArrayList<Ring>(ringlist.availableRings.subList(55, 60)));
			players.get(0).setRingList(ringlistpart1);
			players.get(1).setRingList(ringlistpart2);
			players.get(2).setRingList(ringlistpart3);
		}
		if (this.players.size() == 4) {
			RingList ringlistpart1 = new RingList(new ArrayList<Ring>(ringlist.availableRings.subList(0, 15)));
			RingList ringlistpart2 = new RingList(new ArrayList<Ring>(ringlist.availableRings.subList(15, 30)));
			RingList ringlistpart3 = new RingList(new ArrayList<Ring>(ringlist.availableRings.subList(30, 45)));
			RingList ringlistpart4 = new RingList(new ArrayList<Ring>(ringlist.availableRings.subList(45, 60)));
			players.get(0).setRingList(ringlistpart1);
			players.get(1).setRingList(ringlistpart2);
			players.get(2).setRingList(ringlistpart3);
			players.get(3).setRingList(ringlistpart4);
		}

	}

	private int currentplayer = 0;

	public boolean checkMove(Move move) {
		int choiceField = board.index(move.getX() + 1, move.getY() + 1);
		Tier choiceRing = move.getMoveType();
		Color choiceColor;
		if (Protocol.SECONDARY.equals(move.getColor())) {
			choiceColor = this.players.get(currentplayer).getSecondaryColor();
		} else {
			choiceColor = this.players.get(currentplayer).getPrimaryColor();
		}
		if (board.firstMove) {
			if (board.middle9.stream().anyMatch(a -> a == choiceField)) {
				try {
					this.board.getField(choiceField).placeBase();
				} catch (RinggzException e) {
					return false;
				}
				this.board.firstMove = false;
				return true;
			} else {
				return false;
			}
		} else {
			Ring selectedRing = new Ring(choiceColor, choiceRing);
			try {
				if ((board.isAllowed(choiceField, selectedRing)
						&& board.proximityCheck(choiceField, players.get(currentplayer).getPrimaryColor())
						|| board.fieldHasColor(choiceField, players.get(currentplayer).getPrimaryColor())
								&& this.players.get(currentplayer).ringList.availableRings.contains(selectedRing))) {
					board.setRing(choiceField, selectedRing);
					this.players.get(currentplayer).ringList.availableRings.remove(selectedRing);
					// System.out.println("\nthe ring has been added to the field....");
					return true;
				} else {
					// System.out.println("Invalid move, try another one.");
					return false;
				}
			} catch (RinggzException e) {
				return false;
			}
		}
	}

	public void invalidMove() {

	}

	public void play() {
		Boolean[] canmove = new Boolean[this.players.size()];
		boolean succes = false;
		while (!this.board.boardIsFull() || !Arrays.asList(canmove).stream().noneMatch(a -> a.booleanValue() == true)) {
			while (!succes) {
				try {
					if (players.get(currentplayer).playerCheck(this.board)) {
						players.get(currentplayer).makeMove(this.board);
						canmove[currentplayer] = false;
						succes = true;
					} else {
						canmove[currentplayer] = false;
						succes = true;
					}
				} catch (RinggzException e) {
					succes = false;
				}
			}
			currentplayer += 1;
			currentplayer %= this.players.size();
			succes = false;
		}
		Player winner = null;
		Color colorwin = this.board.isWinner();
		if (this.players.size() == 2) {
			Player one = this.players.get(0);
			Player two = this.players.get(1);
			for (Field field : this.board.fields) {
				if (field.isWinner() == Color.BLUE) {
					Color.BLUE.colorWonFields += 1;
				} else if (field.isWinner() == Color.RED) {
					Color.RED.colorWonFields += 1;
				} else if (field.isWinner() == Color.YELLOW) {
					Color.YELLOW.colorWonFields += 1;
				} else {
					Color.GREEN.colorWonFields += 1;
				}
			}
			one.playerScore = one.getPrimaryColor().colorWonFields + one.getSecondaryColor().colorWonFields;
			two.playerScore = two.getPrimaryColor().colorWonFields + two.getSecondaryColor().colorWonFields;
			if (one.playerScore > two.playerScore) {
				winner = one;
			} else if (two.playerScore > one.playerScore) {
				winner = two;
			} else if (one.playerScore == two.playerScore) {
				System.out.println("It's a tie!"); //aaaaa
			}
			System.out.println("The winner of the match is " + winner.getName());
		} else if (colorwin == null) {
			System.out.println("It is a tie....");
		} else {
			for (Player possiblewinner : this.players) {
				if (possiblewinner.getPrimaryColor() == colorwin) {
					winner = possiblewinner;
					break;
				}
			}
			System.out.println("The winner of the match is " + winner.getName());
		}
	}

	public synchronized boolean addClient(ClientHandler ch) {
		if (this.players.size() < this.maxplayers && this.started == false) {
			this.clients.add(ch);
			ch.linkedgame = this;
			return true;
		} else {
			return false;
		}
	}

	public synchronized void removeClient(ClientHandler ch) {
		ch.linkedgame = null;
		this.clients.remove(ch);
	}
}
