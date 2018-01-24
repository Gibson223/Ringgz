package controller;


import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Collections;

import model.*;

public class NaiveStrategy implements Strategy {

	@Override
	public String getName() {
		return "Naive";
	}
	@Override
	public Field determineField(Color c) {
		Collections.shuffle(c.potentialFields);
		return c.potentialFields.get(0);
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
