package controller;

import java.util.ArrayList;
import java.util.List;

import model.*;

public class ComputerPlayer extends Player {
	
    private Strategy strategy;
    
	public List<Field> potentialFields = new ArrayList<>();

    
    public ComputerPlayer(String name) {
    	super(name);
    	if (name == "SmartStrategy") {
    			this.strategy = new SmartStrategy();    			
    	} else {
    		this.strategy = new NaiveStrategy();
    	}
    }

	@Override
	public void makeMove(Board board) throws RinggzException {
		if (board.firstMove) {
			int fieldChoice = strategy.determineField(board, super.getPrimaryColor()).FieldNumber;
			//CONSTRUCT NEW RING WITH CHOSEN COLOR AND TIER
			Ring ring = new Ring(super.getPrimaryColor(),strategy.determineTier(board.getField(fieldChoice)));
			board.setRing(fieldChoice, ring);
			for (Field field : potentialFields) {
				potentialFields.remove(field);
			}
			potentialFields.add(board.getField(fieldChoice));
			potentialFields.addAll(board.adjacentFields(fieldChoice));

		} else {
			int fieldChoice = strategy.determineField(board, super.getPrimaryColor()).FieldNumber;
			//CONSTRUCT NEW RING WITH CHOSEN COLOR AND TIER
			Ring ring = new Ring(super.getPrimaryColor(),strategy.determineTier(board.getField(fieldChoice)));
			board.setRing(fieldChoice, ring);
			potentialFields.add(board.getField(fieldChoice));
			potentialFields.addAll(board.adjacentFields(fieldChoice));
		}
	}
}
