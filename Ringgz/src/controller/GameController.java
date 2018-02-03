package controller;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
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
	
	public GameController(Server server,int maxplayers) {
		this.server = server;
		this.maxplayers = maxplayers;
		
	}
	public void run() {
		while(!this.started) { // TODO: clean way to stop this loop when server shuts down.
			this.startgame();
		}
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
	private synchronized boolean startGame() throws InterruptedException {
		Collections.shuffle(clients);
		String usernames = "";
		for(ClientHandler client : this.clients) {
			usernames = usernames + Protocol.DELIMITER + client.username;
		}
		for(ClientHandler client : this.clients) {
			client.sendmessage(Packets.ALL_PLAYERS_CONNECTED + usernames);
		}
		long start = System.currentTimeMillis();
		while(!this.clients.stream().allMatch(a -> a.getResponded() == true)) {
			long current = System.currentTimeMillis();
			if(current - start < ALLOWEDDELAY) {
				wait();
			}
		}
		if(!allready()) {
			for(ClientHandler client : this.clients) {
				if(!client.getResponded() || !client.getReady()) {
					removeClient(client);
				}
			}
			for(ClientHandler client : this.clients) {
				client.sendmessage(Packets.JOINED_LOBBY);
			}
			return false;
		} else {
			for(ClientHandler client : this.clients) {
				client.sendmessage((Packets.GAME_STARTED));
			}
			return true;
		}
	}
	private boolean allready() {
		for(ClientHandler handler : this.clients) {
			if(!handler.getResponded() || !handler.getReady()) {
				return false;
			}
		}
		return true;
	}
	public synchronized boolean addPlayer(ClientHandler handler) {
		if(!this.started && this.clients.size() < this.maxplayers) {
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
//		tui = new TUI();
//		for (Field field : board.fields) {
//			field.addObserver(tui);
//		}
		this.playerSetter();
		this.ringdivider();
		tui.view();
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

	public int currentplayer = 0;
	public boolean checkMove(Object[] move) {
		int choiceField = board.index( (Integer) move[0] + 1, (Integer)move[1] + 1);
		Tier choiceRing = Tier.toTier( (Integer) move[2]);
		if (board.firstMove) {
			if (board.middle9.stream().anyMatch(a -> a == choiceField)) {
				board.specialbase(choiceField);
				board.firstMove = false;
				System.out.println("the first move has been placed");
				// ask how to show the view only once in the field if it is a firstmove
				return;
			} else {
				System.out.println("this is the first move and the criteria for this are not met....");
				this.makeMove(board);
				return;
			}
		}
		System.out.println(promptRing);
		int choiceRing = Integer.parseInt(INPUT.nextLine());
		System.out.println(promptColor);
		Color choiceColor = Color.toColor(INPUT.nextLine().charAt(0));
		Ring selectedRing = new Ring(choiceColor, Tier.toTier(choiceRing));

		if ((board.isAllowed(choiceField, selectedRing) && (board.proximityCheck(choiceField, players.get(currentplayer).getPrimaryColor()))
				&& (choiceRing < 6) && (choiceRing > 0) && (choiceColor != null)
				&& this.players.get(currentplayer).ringList.availableRings.contains(selectedRing))) {
			board.setRing(choiceField, selectedRing);
			this.players.get(currentplayer).ringList.availableRings.remove(selectedRing);
			System.out.println("\nthe ring has been added to the field....");
		} else {
			System.out.println("Invalid move, try another one.");
			this.makeMove(board);
		}
	} catch (RinggzException e) {
		this.MakeMove(board);
	} catch (NullPointerException e) {
		System.out.println("invalid color, input your move again:\n");
		this.makeMove(board);
	} catch (NumberFormatException e) {
		System.out.println("invalid input, try again:\n");
		this.makeMove(board);
	}
	}
	public void play() {
		boolean succes = false;
		while (!board.boardIsFull())  
			while (!succes) {
				try {
					players.get(currentplayer).makeMove(board);
					succes = true;
				} catch (RinggzException e) {
				}
			}
			currentplayer += 1;
			currentplayer %= this.players.size();
			succes = false;
		}
	public synchronized boolean addClient(ClientHandler ch) {
		if (this.players.size() < this.maxplayers && this.started == false) {
			this.clients.add(ch);
			ch.linkedgame = this;
			return true;
		}
		else {return false;}
	}
	public synchronized void removeClient(ClientHandler ch) {
		ch.linkedgame = null;
		this.clients.remove(ch);
	}
}
