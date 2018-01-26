package controller;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import model.Board;
import model.Color;
import model.Field;
import model.Ring;
import model.Tier;

public class SmartStrategy implements Strategy {

	public String getName() {
		return "Smart";
	}

	public Field determineField(Board board, Player p) {
		Collections.shuffle(p.potentialFields);
		Field smartField = p.potentialFields.get(0);
		if (board.firstMove) {
			try {
				p.potentialFields.addAll(Arrays.asList(board.getField(7), board.getField(8), board.getField(9),
						board.getField(12), board.getField(13), board.getField(14), board.getField(17),
						board.getField(18), board.getField(19)));
			} catch (RinggzException e) {
				e.printStackTrace();
			}
		}
		boolean fieldFound = false;
		while (!fieldFound) {
			int frec = Collections.frequency(smartField.getFieldColors(), p.getPrimaryColor());
			if (frec > 2) {
				determineField(board, p);
			} else {
				fieldFound = true;
			}
		}
		return smartField;
	}

	@Override
	public Tier determineTier(Field f) {
		List<Tier> availableTiers = new ArrayList<>();
		availableTiers.removeAll(availableTiers);
		for (Ring ring : f.getFieldState()) {
			if (ring.getColor() == Color.INIT) {
				availableTiers.add(ring.getTier());
			}
		}
		Collections.shuffle(availableTiers);
		return availableTiers.get(0);
	}
}
