package controller;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import model.*;

public class ComputerPlayer extends Player {
	
    private Strategy strategy;
    
	public List<Field> potentialFields = new ArrayList<>();

    
    public ComputerPlayer(String name) {
    	super(name);
    	if (name == "SmartStrategy") {
    		this.strategy = new SmartStrategy();
    	}
    }

	@Override
	public void makeMove(Board board) throws RinggzException {
		try {
			int choiceField = (int) (Math.floor(Math.random() * 25) + 1);
			List<Color> colors = new ArrayList<>();
			colors.add(this.getPrimaryColor());
			colors.add(this.getSecondaryColor());				
			Collections.shuffle(colors);
			Color choiceColor = colors.get(0);
			List<Tier> tiers = new ArrayList<Tier>(Arrays.asList(Tier.values()));
			Collections.shuffle(tiers);
			Tier choiceTier = tiers.get(0);
			Ring selectedRing = new Ring(choiceColor, choiceTier);
			if (board.firstMove) {
				int  tempfield = choiceField;
				if (board.middle9.stream().anyMatch(a -> a == tempfield)) {
					board.specialbase(choiceField);
					board.firstMove = false;
					System.out.println("\nthe first move has been placed");
				}
			} else {
				if (board.isAllowed(choiceField, selectedRing) && 
						(board.proximityCheck(choiceField, getPrimaryColor()))
						&& (choiceColor != null) 
						&& this.ringList.availableRings.contains(selectedRing)) {
					board.setRing(choiceField, selectedRing);
					this.ringList.availableRings.remove(selectedRing);
					potentialFields.add(board.getField(choiceField));
					potentialFields.addAll(board.adjacentFields(choiceField));
					System.out.println("\nthe ring has been added to the field....");
				}
			}
		} catch (RinggzException e) {
			this.makeMove(board);
		} catch (NullPointerException e) {
			System.out.println("invalid color, input your move again:\n");
			this.makeMove(board);
		} catch (NumberFormatException e) {
			System.out.println("invalid input, try again:\n");
			this.makeMove(board); 
		}
	}
}
