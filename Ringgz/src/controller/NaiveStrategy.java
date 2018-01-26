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
		try {
			p.potentialFields.addAll(Arrays.asList(board.getField(7), board.getField(8), board.getField(9),
					board.getField(12), board.getField(13), board.getField(14), board.getField(17), board.getField(18),
					board.getField(19)));
		} catch (RinggzException e) {
			e.printStackTrace();
		}
		Collections.shuffle(p.potentialFields);
		return p.potentialFields.get(0);
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

	@Override
	public Color determineColor(Board board, Player p) {
		List<Color> colors = new ArrayList<>();
		colors.add(p.getPrimaryColor());
		colors.add(p.getSecondaryColor());
		Collections.shuffle(colors);
		return colors.get(0);
	}
}
