package controller;

import model.*;
import view.*;
import controller.*;

public class GameController implements Runnable {
	public Player[] players;
	public Board board;
	public TUI tui;
	public RingList ringlist = new RingList();
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
	public GameController(HumanPlayer humanPlayer, HumanPlayer humanPlayer2) {
		
	}
	@Override
	public void run() {
		for  (Field field: board.fields) {
			field.addObserver(tui);
		}
		board = new Board();
		tui = new TUI(this.board);
        tui.start();
	}
	public static void main(String[] args) {
		GameController gc = new GameController(
				new HumanPlayer("Gibson", Color.BLUE, Color.YELLOW, gc.ringlist),
				new HumanPlayer("Random", Color.GREEN, Color.RED, gc.ringlist));
	}
	
}
