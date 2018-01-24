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
		board = new Board();
		tui = new TUI(this.board);
		ringlist = new RingList();
        players = new Player[3];
        players[0] = new HumanPlayer("Gibson", Color.BLUE, ringlist);
        players[1] = s1;
        players[2] = s2;
        players[3] = s3;
	}
	@Override
	public void run() {
        tui.start();
	}
	
}
