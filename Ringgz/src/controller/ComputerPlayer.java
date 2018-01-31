package controller;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import model.*;

public class ComputerPlayer extends Player {
	
    private Strategy strategy;

    public List<Field> potentialFields;
    
    public ComputerPlayer(String name) {
    	super(name);
    	if (name == "SmartStrategy") {
    			this.strategy = new SmartStrategy();    			
    	} else {
    		this.strategy = new NaiveStrategy();
    	}
    	List<Field> potentialFields = new ArrayList<>();	
    }

	@Override
	public void makeMove(Board board) throws RinggzException {
		try {
			int choiceField = strategy.determineField(board, this).FieldNumber;
			//CONSTRUCT NEW RING WITH CHOSEN COLOR AND TIER
			Color choiceColor = strategy.determineColor(board, this);
			Tier choiceTier = strategy.determineTier(board,board.getField(choiceField),this);
			Ring selectedRing = new Ring(choiceColor, choiceTier);
			if (board.firstMove) {
				int  tempfield = choiceField;
				if (board.middle9.stream().anyMatch(a -> a == tempfield)) {
					board.specialbase(choiceField);
					board.firstMove = false;
					System.out.println("the first move has been placed");
					potentialFields.add(board.getField(choiceField));
					potentialFields.addAll(board.adjacentFields(choiceField));
					// ask how to show the view only once in the field if it is a firstmove
				} else {
					System.out.println(
							"this is the first move and the criteria for this are not met...");
					this.makeMove(board);
				}
			} else {
				choiceField = strategy.determineField(board, this).FieldNumber;
				//CONSTRUCT NEW RING WITH CHOSEN COLOR AND TIER
				choiceColor = strategy.determineColor(board, this);
				choiceTier = strategy.determineTier(board,board.getField(choiceField),this);
				selectedRing = new Ring(choiceColor, choiceTier);
				if ( (board.isAllowed(choiceField, selectedRing) && 
						(board.proximityCheck(choiceField, getPrimaryColor()))
						&& (choiceColor != null) 
						&& this.ringList.availableRings.contains(selectedRing))) {
					board.setRing(choiceField, selectedRing);
					this.ringList.availableRings.remove(selectedRing);
					potentialFields.add(board.getField(choiceField));
					potentialFields.addAll(board.adjacentFields(choiceField));
					System.out.println("\nthe ring has been added to the field....");
				} else {
					this.makeMove(board);
				}
			}
		}catch (RinggzException e) {
			this.makeMove(board);
		} catch (NullPointerException e) {
			System.out.println("invalid color, input your move again:\n");
			this.makeMove(board);
		} catch (NumberFormatException e) {
			System.out.println("invalid input, try again:\n");
			this.makeMove(board);}
	}
}
