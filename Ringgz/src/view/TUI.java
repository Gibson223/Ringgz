package view;
import java.util.Observable;
import java.util.Observer;
import java.util.Scanner;

import controller.RinggzException;
import model.Board;
import model.Color;
import model.Field;
import model.Ring;
import model.Tier;

public class TUI implements Observer, Runnable {
	
	private Board board;
	
	public TUI(Board board) {
		this.board = board;
	}
	public void view() { 
		for (Field field: board.fields) {
			if (((field.FieldNumber - 1) % 5) == 0) {
				System.out.print("\n \n" + "|");				
			}
			System.out.print(field.toString() + "|");
		}
	}
	
	@Override
	public void update(Observable arg0, Object arg1) {
		if (arg0 instanceof Field && arg1 instanceof String && 
				("ring placed".equals((String) arg1))) {
			this.view();
		}
	}
	public void run() {
		this.view();
		System.out.println("\n");
//		boolean exit = false;
//		while(!exit) {
//			Scanner in = new Scanner(System.in);
//			
//		}
	}


}
