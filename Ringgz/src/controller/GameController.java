package controller;

import java.util.ArrayList;

import java.util.List;

import model.Board;
import model.Color;
import model.Field;
import model.Ring;
import model.RingList;
import view.TUI;

public class GameController implements Runnable {
	public List<Player> players = new ArrayList<Player>();
	public Board board;
	public TUI tui;
	public RingList ringlist;

	public GameController(Player s0, Player s1, Player s2, Player s3) {
		List<Object> playerlist = new ArrayList<>();
		playerlist.add(s0);
		playerlist.add(s1);
		playerlist.add(s2);
		playerlist.add(s3);
		playerlist.stream().filter(a -> a != null).forEach(a -> players.add((Player) a));
		this.run();
	}

	@Override
	public void run() {
		board = new Board();
		ringlist = new RingList();
		tui = new TUI();
//		for (Field field : board.fields) {
//			field.addObserver(tui);
//		}
		this.playerSetter();
		this.ringdivider();
		//tui.start();
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

	public void play() {
		boolean succes = false;
		while (!board.boardIsFull()) {
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
	}
}
