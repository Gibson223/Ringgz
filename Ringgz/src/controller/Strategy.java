package controller;
import model.Board;
import model.Color;
import model.Ring;

public interface Strategy {
	
	public String getName();
	public int determineMove(Board b, Ring r);

}
