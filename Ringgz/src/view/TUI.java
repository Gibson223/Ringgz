package view;
import java.util.Observable;
import java.util.Observer;

import controller.RinggzException;
import model.Board;
import model.Color;
import model.Field;
import model.Ring;
import model.Tier;

public class TUI implements Observer {
	
	private Board board;
	
	public TUI(Board board) {
		this.board = board;
	}
	public void view () { 
		for (Field field: board.fields) {
			if (((field.FieldNumber-1) % 5) == 0) {
					System.out.print("\n\n" + "|");				
				}
			System.out.print( field.toString() + "|");
		}
	}
	public static void main(String[] args) {
		Board b = new Board();
		TUI tui = new TUI(b);
		Ring ring = new Ring(Color.BLUE, Tier.BASE);
		Ring ring1 = new Ring(Color.GREEN, Tier.BASE);
		Ring ring2= new Ring(Color.BLUE, Tier.BASE);
		Ring ring3 = new Ring(Color.BLUE, Tier.BASE);
		try {
			b.setRing(2, ring);
			b.setRing(4, ring1);
			b.setRing(6, ring2);
			b.setRing(8, ring3);
		} catch (RinggzException e) {
		}
		tui.view();
	}
	@Override
	public void update(Observable arg0, Object arg1) {
		if (arg0 instanceof Field && arg1 instanceof String && ("ring placed".equals(((String)arg1)))) {
			this.view();
		}
	}


}
