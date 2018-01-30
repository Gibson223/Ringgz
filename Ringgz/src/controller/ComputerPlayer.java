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
		int choiceField = strategy.determineField(board, this).FieldNumber;
		//CONSTRUCT NEW RING WITH CHOSEN COLOR AND TIER
		Color choiceColor = strategy.determineColor(board, this);
		Tier choiceTier = strategy.determineTier(board.getField(choiceField));
		Ring selectedRing = new Ring(choiceColor, choiceTier);
		if (board.firstMove) {
			try {
			if ( (board.isAllowed(choiceField, selectedRing) && 
					(board.proximityCheck(choiceField, getPrimaryColor()))
					&& (choiceColor != null) 
					&& this.ringList.availableRings.contains(selectedRing))) {
				board.specialbase((choiceField));
				this.ringList.availableRings.remove(selectedRing);
				System.out.println("\nthe ring has been added to the field....");
			} else {
				System.out.println("Invalid move, try another one.");
				this.makeMove(board);
			}
		}catch (RinggzException e) {
			this.makeMove(board);
		} catch (NullPointerException e) {
			System.out.println("invalid color, input your move again:\n");
			this.makeMove(board);
		} catch (NumberFormatException e) {
			System.out.println("invalid input, try again:\n");
			this.makeMove(board);}
			potentialFields.add(board.getField(choiceField));
			potentialFields.addAll(board.adjacentFields(choiceField));
		} else {
			choiceField = strategy.determineField(board, this).FieldNumber;
			//CONSTRUCT NEW RING WITH CHOSEN COLOR AND TIER
			choiceColor = strategy.determineColor(board, this);
			choiceTier = strategy.determineTier(board.getField(choiceField));
			selectedRing = new Ring(choiceColor, choiceTier);
			try {
			if ( (board.isAllowed(choiceField, selectedRing) && 
					(board.proximityCheck(choiceField, getPrimaryColor()))
					&& (choiceColor != null) 
					&& this.ringList.availableRings.contains(selectedRing))) {
				board.setRing(choiceField, selectedRing);
				this.ringList.availableRings.remove(selectedRing);
				System.out.println("\nthe ring has been added to the field....");
			} else {
				System.out.println("Invalid move, try another one.");
				this.makeMove(board);
			}
		}catch (RinggzException e) {
			this.makeMove(board);
		} catch (NullPointerException e) {
			System.out.println("invalid color, input your move again:\n");
			this.makeMove(board);
		} catch (NumberFormatException e) {
			System.out.println("invalid input, try again:\n");
			this.makeMove(board);}	
			
			potentialFields.add(board.getField(choiceField));
			potentialFields.addAll(board.adjacentFields(choiceField));
		}
	}
}
