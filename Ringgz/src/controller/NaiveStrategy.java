package controller;

import model.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class NaiveStrategy implements Strategy {

	@Override
	public String getName() {
		return "Naive";
	}

	@Override
	public Field determineField(Board board, Player p) {
		if (board.firstMove) {
			List<Integer> fields = new ArrayList<>(board.middle9);
			
			Collections.shuffle(fields);
			try {
				return board.getField(fields.get(0));
			} catch (RinggzException e) {
				determineField(board , p);
				e.printStackTrace();
			}
		}
		Collections.shuffle(p.potentialFields);
		return p.potentialFields.get(0);
	}

	@Override
	public Tier determineTier(Board b, Field f, Player p) {
		List<Tier> availableTiers = new ArrayList<>();
		availableTiers.removeAll(availableTiers);
		for (Ring ring : f.getFieldState()) {
			if (ring.getColor() == Color.INIT) {
				availableTiers.add(ring.getTier());
			}
		}
		if (availableTiers != null) {
			
		}
		Collections.shuffle(availableTiers);
		return availableTiers.get(0);
	}

	@Override
	public Color determineColor(Board board, Player p) {
		List<Color> colors = new ArrayList<>();
		colors.add(p.getPrimaryColor());
		colors.add(p.getSecondaryColor());
		Collections.shuffle(colors);
		return colors.get(0);
	}
}
