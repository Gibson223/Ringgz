package view;
import java.util.Observable;
import java.util.Observer;

import model.Board;
import model.Field;

public class TUI implements Observer {
	
	private Board board;
	
	public TUI(Board board) {
		this.board = board;
	}

	public void view () { 
		for (Field field: board.fields) {
			if (((field.FieldNumber-1) % 5) == 0) {
					System.out.print("\n|");				
				}
			System.out.print( field.toString() + "|");
		}
	}
	public static void main(String[] args) {
		Board b = new Board();
		TUI tui = new TUI(b);
//		Ring ring = new Ring();
		tui.view();
	}
	@Override
	public void update(Observable arg0, Object arg1) {
		
	}
}
