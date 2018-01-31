package controller;
import model.Board;
import model.*;

public interface Strategy {
	
	public String getName();
	public Object[] determineMove();
	public Field determineField(Board board, Player p);
	public Tier determineTier(Board board, Field f, Player p);
	public Color determineColor(Board board, Player p);
}
