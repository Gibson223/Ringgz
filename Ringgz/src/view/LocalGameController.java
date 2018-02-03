package view;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import controller.GameController;
import controller.Move;
import controller.Player;
import controller.RinggzException;
import model.Board;
import model.Color;
import model.Field;
import model.Ring;
import model.RingList;

public class LocalGameController implements Runnable{
	private InetAddress adress;
	private String username;
	private int port;
	private TUI tui;
	private Socket clientsocket;
	private boolean gamestarted;
	public LocalGameController(TUI tui, String username, InetAddress adress, int port) throws IOException {
		this.adress = adress;
		this.tui = tui;
		this.username = username;
		this.port = port;
		this.clientsocket = new Socket(adress, port);
		this.run();
	}
//	private 
//	private boolean establishConnection() {
//		while() {
//			
//	}
	
	public List<Player> players = new ArrayList<Player>();
	public Board board;
	public RingList ringlist;
	private Map<Player, Boolean> canmove;
	public int currentplayer = 0;
	
	@Override
	public void run() {
		board = new Board();
		ringlist = new RingList();
		tui = new TUI(this.board);
		for  (Field field: board.fields) {
			field.addObserver(tui);
		}
		this.playerSetter();
		this.ringdivider();
		Thread tuithread = new Thread(tui);
		tui.run();
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
			RingList ringlistpart1 = new RingList(
					new ArrayList<Ring>(ringlist.availableRings.subList(0, 30)));
			RingList ringlistpart2 = new RingList(
					new ArrayList<Ring>(ringlist.availableRings.subList(30, 60)));
			players.get(0).setRingList(ringlistpart1);
			players.get(1).setRingList(ringlistpart2);
		}
		if (this.players.size() == 3) {
			RingList ringlistpart1 = new RingList(new ArrayList<Ring
					>(ringlist.availableRings.subList(0, 15)));
			RingList ringlistpart2 = new RingList(new ArrayList<Ring>(
				ringlist.availableRings.subList(15, 30)));
			RingList ringlistpart3 = new RingList(new ArrayList<Ring>(
				ringlist.availableRings.subList(30, 45)));
			ringlistpart1.availableRings.addAll(new ArrayList<Ring>(
				ringlist.availableRings.subList(45, 50)));
			ringlistpart2.availableRings.addAll(new ArrayList<Ring>(
				ringlist.availableRings.subList(50, 55)));
			ringlistpart3.availableRings.addAll(new ArrayList<Ring>(
				ringlist.availableRings.subList(55, 60)));
			players.get(0).setRingList(ringlistpart1);
			players.get(1).setRingList(ringlistpart2);
			players.get(2).setRingList(ringlistpart3);
		}
		if (this.players.size() == 4) {
			RingList ringlistpart1 = new RingList(
					new ArrayList<Ring>(ringlist.availableRings.subList(0, 15)));
			RingList ringlistpart2 = new RingList(
					new ArrayList<Ring>(ringlist.availableRings.subList(15, 30)));
			RingList ringlistpart3 = new RingList(
					new ArrayList<Ring>(ringlist.availableRings.subList(30, 45)));
			RingList ringlistpart4 = new RingList(
					new ArrayList<Ring>(ringlist.availableRings.subList(45, 60)));
			players.get(0).setRingList(ringlistpart1);
			players.get(1).setRingList(ringlistpart2);
			players.get(2).setRingList(ringlistpart3);
			players.get(3).setRingList(ringlistpart4);
		}
		
	}
	public boolean handleMove(Move move) {
		return true;
	}
	public void play() {
		boolean succes = false;
		while (!this.board.boardIsFull() || !canmove.values().
				stream().allMatch(a -> a.booleanValue() == false)) {
			while (!succes) {
				try {
					if (players.get(currentplayer).playerCheck()) {
						players.get(currentplayer).makeMove(board);
						canmove.put(players.get(currentplayer), true);
						succes = true;
					} else {
						canmove.put(players.get(currentplayer), false);
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
		if (colorwin == null) {
			System.out.println("It is a tie....");
		} else {
			for (Player possiblewinner: this.players) {
				if (possiblewinner.getPrimaryColor() == colorwin) {
					winner = possiblewinner;
					break;
				}
			}
			System.out.println("The winner of the match is " + winner.getName());
		}
	}
}
