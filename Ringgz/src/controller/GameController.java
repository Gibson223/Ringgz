package controller;

import model.*;
import view.*;
import controller.*;

public class GameController implements Runnable {
	public Player[] players;
	public Board board;
	public TUI tui;
	public RingList ringlist;
	// we get the name from the packets
	//TODO ask question how to add observers to all fields of the board
	public GameController( Player s0, Player s1, Player s2, Player s3) {
        players = new Player[4];
        players[0] = s0;
        players[1] = s1;
        players[2] = s2;
        players[3] = s3;
        this.run();
	}
	public GameController(Player player, Player player2) {
		players = new Player[2];
		players[0] = player;
        players[1] = player2;
        this.run();
	}
	public GameController(Player player, Player player2, Player player3) {
		players = new Player[3];
		players[0] = player;
        players[1] = player2;
        players[2] = player3;
        this.run();
	}
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
        tui.start();
		this.play();

	}
	public void playerSetter() {
		if (this.players.length == 2) {
			players[0].setPrimary(Color.RED);
			players[0].setSecondary(Color.YELLOW);
			players[1].setPrimary(Color.GREEN);
			players[1].setSecondary(Color.BLUE);
		}
		if(this.players.length == 3) {
			players[0].setPrimary(Color.RED);
			players[1].setPrimary(Color.YELLOW);
			players[2].setPrimary(Color.GREEN);
			players[0].setSecondary(Color.BLUE);
			players[1].setSecondary(Color.BLUE);
			players[2].setSecondary(Color.BLUE);
		}
		if(this.players.length == 4) {
			players[0].setPrimary(Color.RED);
			players[1].setPrimary(Color.YELLOW);
			players[2].setPrimary(Color.GREEN);
			players[2].setPrimary(Color.BLUE);			
		}
	}
	public void ringdivider() {
		if (this.players.length == 2){
			RingList ringlistpart1 = new RingList(ringlist.availableRings.subList(0, 30));
			RingList ringlistpart2 = new RingList(ringlist.availableRings.subList(30, 60));
			players[0].setRingList(ringlistpart1);
			players[1].setRingList(ringlistpart2);
		}
		if (this.players.length == 3) {
			RingList ringlistpart1 = new RingList(ringlist.availableRings.subList(0, 15));
			RingList ringlistpart2 = new RingList(ringlist.availableRings.subList(15, 30));
			RingList ringlistpart3 = new RingList(ringlist.availableRings.subList(30, 45));
			ringlistpart1.availableRings.addAll(ringlist.availableRings.subList(45, 50));
			ringlistpart2.availableRings.addAll(ringlist.availableRings.subList(50, 55));
			ringlistpart3.availableRings.addAll(ringlist.availableRings.subList(55, 60));
			players[0].setRingList(ringlistpart1);
			players[1].setRingList(ringlistpart2);
			players[2].setRingList(ringlistpart3);
		}
		if(this.players.length == 4) {
			RingList ringlistpart1 = new RingList(ringlist.availableRings.subList(0, 15));
			RingList ringlistpart2 = new RingList(ringlist.availableRings.subList(15, 30));
			RingList ringlistpart3 = new RingList(ringlist.availableRings.subList(30, 45));
			RingList ringlistpart4 = new RingList(ringlist.availableRings.subList(45, 60));
			players[0].setRingList(ringlistpart1);
			players[1].setRingList(ringlistpart2);
			players[2].setRingList(ringlistpart3);
			players[3].setRingList(ringlistpart4);
		}
		
	}
	public int currentplayer = 0;
	public void play(){
		boolean succes = false;
		while(!board.boardIsFull()) {
			while(!succes) {
					try {
						players[currentplayer].makeMove(board);
						succes = true;
					} catch (RinggzException e) {}
			}
			currentplayer += 1;
        	currentplayer %= this.players.length;
        	succes = false;
        }
	}
}
