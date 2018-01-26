package controller;
import model.Board;
import model.Color;
import model.*;
import java.util.ArrayList;
import java.util.List;

public interface Strategy {
	
	public String getName();
	public Field determineField(Board board, Player p);
	public Tier determineTier(Field f);
}
