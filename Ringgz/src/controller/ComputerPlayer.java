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
			int choiceField = strategy.determineField(board, this).FieldNumber;
			// CONSTRUCT NEW RING WITH CHOSEN COLOR AND TIER
			Color choiceColor = strategy.determineColor(board, this);
			Tier choiceTier = strategy.determineTier(board.getField(choiceField));
			Ring selectedRing = new Ring(choiceColor, choiceTier);
			try {
				if (board.isAllowed(choiceField, selectedRing)
						&& (board.proximityCheck(choiceField, getPrimaryColor()))
						&& (choiceColor != null)
						&& this.ringList.availableRings.contains(selectedRing)) {
					board.setRing(choiceField, selectedRing);
					this.ringList.availableRings.remove(selectedRing);
					System.out.println("\nthe ring has been added to the field....");
				} else {
					this.makeMove(board);
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
			potentialFields.add(board.getField(choiceField));
			potentialFields.addAll(board.adjacentFields(choiceField));

		} else {
			int choiceField = strategy.determineField(board, this).FieldNumber;
			// CONSTRUCT NEW RING WITH CHOSEN COLOR AND TIER
			Color choiceColor = strategy.determineColor(board, this);
			Tier choiceTier = strategy.determineTier(board.getField(choiceField));
			Ring selectedRing = new Ring(choiceColor, choiceTier);
			try {
				if (board.isAllowed(choiceField, selectedRing)
						&& (board.proximityCheck(choiceField, getPrimaryColor()))
						&& (choiceColor != null)
						&& this.ringList.availableRings.contains(selectedRing)) {
					board.setRing(choiceField, selectedRing);
					this.ringList.availableRings.remove(selectedRing);
					System.out.println("\n \n the Computer has added a ring to the field....");
				} else {
					this.makeMove(board);
				}
			} catch (RinggzException e) {
				this.makeMove(board);
			} catch (NullPointerException e) {
				this.makeMove(board);
			} catch (NumberFormatException e) {
				this.makeMove(board);
			}

			potentialFields.add(board.getField(choiceField));
			potentialFields.addAll(board.adjacentFields(choiceField));
		}
	}
}
