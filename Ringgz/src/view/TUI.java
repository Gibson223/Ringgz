package view;
import model.Board;

public class TUI {
	
	private Board board;
	
	public TUI(Board board) {
		this.board = board;
	}

	public static void main (String[] args) {
		System.out.println("      |      |      |      |      ");
		System.out.println(     " | "    " | "    " | "    " | " + );
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
}
