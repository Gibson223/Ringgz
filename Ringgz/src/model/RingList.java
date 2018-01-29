package model;

import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

public class RingList {
	public List<Ring> availableRings = new LinkedList<>();

	public RingList() {
		for (Color c : Color.values()) {
			for (int i = 0; i < 3; i++) {
				for (Tier tier : Tier.values()) {
					availableRings.add(new Ring(c, tier));
				}
			}
		}
		availableRings = availableRings.stream().filter(a -> a.getColor() != Color.INIT).collect(Collectors.toList());
		availableRings = availableRings.stream().filter(a -> a.getTier() != Tier.INIT).collect(Collectors.toList());
	}

	public RingList(List<Ring> availablerings) {
		this.availableRings = availablerings;
	}
}