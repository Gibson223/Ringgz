package controller;

import model.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Collections;

public class NaiveStrategy implements Strategy {

	@Override
	public String getName() {
		return "Naive";
	}
	public Field determineField(Board board, Color c) {
		try {
			potentialFields.addAll(Arrays.asList(board.getField(7), board.getField(8), board.getField(9), board.getField(12), board.getField(13), board.getField(14), board.getField(17), board.getField(18), board.getField(19)));
		} catch (RinggzException e) {
			e.printStackTrace();
		}
		Collections.shuffle(potentialFields);
		return potentialFields.get(0);
	}

	@Override
	public Tier determineTier(Field f) {
		List <Tier> availableTiers = new ArrayList<>();
		for (Ring ring : f.getFieldState()) {
			if (ring.getColor() == null) {
				availableTiers.add(ring.getTier());
			}
		}
		Collections.shuffle(availableTiers);
		return availableTiers.get(0);
	}
}
