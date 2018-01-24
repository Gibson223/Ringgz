package view;
import java.util.Observable;
import java.util.Observer;

import model.Board;

public class TUI implements Observer {
	
	private Board board;
	
	public TUI(Board board) {
		this.board = board;
	}

	public static void main (String[] args) {
		
		System.out.println("      |      |      |      |      ");
		System.out.println("      |      |      |      |      ");
		System.out.println("      |      |      |      |      ");
		System.out.println("------+------+------+------+------");
		System.out.println("      |      |      |      |      ");
		System.out.println("      |      |      |      |      ");
		System.out.println("      |      |      |      |      ");
		System.out.println("------+------+------+------+------");
		System.out.println("      |      |      |      |      ");
		System.out.println("      |      |      |      |      ");
		System.out.println("      |      |      |      |      ");
		System.out.println("------+------+------+------+------");
		System.out.println("      |      |      |      |      ");
		System.out.println("      |      |      |      |      ");
		System.out.println("      |      |      |      |      ");
		System.out.println("------+------+------+------+------");
		System.out.println("      |      |      |      |      ");
		System.out.println("      |      |      |      |      ");
		System.out.println("      |      |      |      |      ");
	}

	@Override
	public void update(Observable arg0, Object arg1) {
		// TODO Auto-generated method stub
		
	}
}
