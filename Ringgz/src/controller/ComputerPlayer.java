package controller;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import model.*;
import serverclient.Protocol;

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
	public Move makeMove(Board board) throws RinggzException {
		boolean succes = false;
		int choiceField = 0;
		Color choiceColor;
		int choiceRing = 0;
		String colorProtocol = null;
		while (!succes) {
		try {
			choiceField = (int) (Math.floor(Math.random() * 25) + 1);
			List<Color> colors = new ArrayList<>();
			colors.add(this.getPrimaryColor());
			colors.add(this.getSecondaryColor());				
			Collections.shuffle(colors);
			choiceColor = colors.get(0);
			if (choiceColor == this.getPrimaryColor()) {
				colorProtocol = Protocol.PRIMARY;
			} else {
				colorProtocol = Protocol.SECONDARY;
			}
			choiceRing = (int) (Math.floor(Math.random() * 5) + 1);
			Tier choiceTier = Tier.toTier(choiceRing);
			Ring selectedRing = new Ring(choiceColor, choiceTier);
			if (!this.ringList.availableRings.contains(new Ring(choiceColor, choiceTier))
					&& !board.isAllowed(choiceField, selectedRing)) {
				succes = true;
			}
			if (board.firstMove) {
				int  tempfield = choiceField;
				if (board.middle9.stream().anyMatch(a -> a == tempfield)) {
					board.specialBase(choiceField);
					board.firstMove = false;
					System.out.println("the first move has been placed");
					succes = true;
				} else {
					System.out.println(
							"this is the first move and the criteria for this are not met...");
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
					succes = true;
				} else {
					System.out.println("Invalid move, try another one.");
				}
			}
		} catch (RinggzException e) {
		} catch (NullPointerException e) {
		} catch (NumberFormatException e) {
		}
		}
	return new Move(Board.xy(choiceField)[0], Board.xy(choiceField)[1], choiceRing ,colorProtocol);
	}
}