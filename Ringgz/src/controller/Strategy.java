package controller;
import model.Board;
import model.*;

public interface Strategy {
	
	public String getName();
	public Field determineField(Board board, Player p);
	public Tier determineTier(Field f);
	public Color determineColor(Board board, Player p);
}
