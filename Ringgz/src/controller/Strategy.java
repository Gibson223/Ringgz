package controller;
import model.Board;
import model.Color;
import model.Ring;
import model.*;

public interface Strategy {
	
	public String getName();
	public int determineMove(Board b, Ring r);
	public Field determineField(Color c);// returns adjacent fields minus full fields
	public Tier determineTier(Field f);

}
