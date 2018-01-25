package controller;

import model.*;
import view.*;

public class GameController implements Runnable {
	public Player[] players;
	public Board board;
	public TUI tui;
	public RingList ringlist;
	// we get the name from the packets
	//TODO ask question how to add observers to all fields of the board
	public GameController( Player s0, Player s1, Player s2, Player s3) {
//		ringlist = new RingList();
        players = new Player[3];
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
	@Override
	public void run() {
		board = new Board();
		ringlist = new RingList();
		tui = new TUI(this.board);
		for  (Field field: board.fields) {
			field.addObserver(tui);
		}
		this.playerSetter();
//		this.ringdivider();
        tui.start();
		this.play();

	}
	public void playerSetter() {
		if (this.players.length == 2) {
//			ringlistpart1 = new ArrayList<Ring>(this.ringlist);
			players[0].setPrimary(Color.BLUE);
			players[0].setSecondary(Color.GREEN);
			players[0].setRingList(ringlist);
			players[1].setPrimary(Color.RED);
			players[1].setSecondary(Color.YELLOW);
			players[1].setRingList(ringlist);
		}
	}
	public void ringdivider() {
		
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
