package model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Observable;

public class Field extends Observable {
	public final int FieldNumber;

	public void placeBase() {
		this.fieldState.clear();
		this.fieldState.add(new Ring(Color.BLUE, Tier.SMALL));
		this.fieldState.add(new Ring(Color.GREEN, Tier.MEDIUM));
		this.fieldState.add(new Ring(Color.RED, Tier.LARGE));
		this.fieldState.add(new Ring(Color.YELLOW, Tier.LARGEST));
		setChanged();
		notifyObservers("ring placed");
	}

	public Field() {
		this.initfieldState();
	}

	public void initfieldState() {
		fieldState.add(new Ring(Color.INIT, Tier.SMALL));
		fieldState.add(new Ring(Color.INIT, Tier.MEDIUM));
		fieldState.add(new Ring(Color.INIT, Tier.LARGE));
		fieldState.add(new Ring(Color.INIT, Tier.LARGEST));
	}

	// small to large;
	// 1 = small
	// 4 = large;
	private List<Ring> fieldState = new ArrayList<>();

	public List<Ring> getFieldState() {
		return fieldState;
	}

	// ROW-COLUMN ADAPTATION FOR getFieldState ABOVE

	// RETURNS WHETHER OR NOT A FIELD HAS A CERTAIN COLOR RING
	// for proximity check
	public boolean HasColor(Color color) {
		for (Ring ring : fieldState) {
			if (ring.getColor() == color) {
				return true;
			}
		}
		return false;
	}

	public boolean HasBase() {
		for (Ring ring : fieldState)
			if (ring.getTier() == Tier.BASE && ring.getColor() != Color.INIT) {
				return true;
			}
		return false;
	}

	public boolean isFull() {
		if (this.HasBase()) {
			return true;
		}
		for (Ring ring : fieldState) {
			if (!ring.getTier().occupied() || ring.getColor() != Color.INIT) {
				return false;
			}
		}
		return false;
	}

	public boolean isAllowed(Ring r) {
		if (this.isFull()) {
			return false;
		}
		for (Ring ring : fieldState) {
			if (ring.getTier() == r.getTier() && !(ring.getColor() == Color.INIT)) {
				return false;
			}
		}
		return true;
	}

	public void setRing(Ring ring) {
		if (this.isAllowed(ring)) {
			if (ring.getTier() == Tier.BASE) {
				fieldState.set(3, ring);
			}
			for (int i = 0; i < 4; i++) {
				if (this.fieldState.get(i).getTier() == ring.getTier()) {
					this.fieldState.set(i, ring);
				}
			}
			setChanged();
			notifyObservers("ring placed");

		}
	}

	public Color isWinner() {
		Map<Color, Integer> map = new HashMap<>();
		for (Ring f : fieldState) {
			if (map.containsKey(f.getColor())) {
				map.put(f.getColor(), map.get(f.getColor()) + 1);
			} else {
				map.put(f.getColor(), new Integer(1));
			}
		}
		map.remove(Color.INIT);
		System.out.println(map);
		Integer highest = java.util.Collections.max(map.values());
		if (java.util.Collections.frequency(map.values(), highest) == 1) {
			for (Map.Entry<Color, Integer> c : map.entrySet()) {
				if (c.getValue() == highest) {
					return c.getKey();
				}
			}
		}
		return null;
	}

	public List<Color> getFieldColors() {
		List<Color> result = new ArrayList<>();
		for (Ring ring : this.getFieldState()) {
			result.add(ring.getColor());
		}
		return result;
	}

	public String toString() {
		if (this.fieldState.stream().allMatch(a -> (a.getColor() == Color.INIT && this.FieldNumber < 10))) {
			return "--" + this.FieldNumber + "-";
		}
		if (this.fieldState.stream().allMatch(a -> (a.getColor() == Color.INIT))) {
			return "-" + this.FieldNumber + "-";
		}
		if (this.HasBase() == true) {
			return "" + fieldState.get(3).getColor() + "BAS";
		}
		String result = "";
		for (Ring ring : this.fieldState) {
			result += ring.toString();
		}

		return result;

	}

	// public static void main(String[] args) {
	// Field a = new Field();
	// Ring ring = new Ring(Color.BLUE, Tier.MEDIUM);
	// Ring ring2 = new Ring(Color.GREEN, Tier.SMALL);
	// Ring ring3 = new Ring(Color.GREEN, Tier.LARGE);
	// System.out.println(ring);
	// System.out.println(a.FieldNumber);
	// System.out.println(a.fieldState);
	// a.setRing(ring);
	// System.out.println(a.fieldState);
	// a.setRing(ring);
	// a.setRing(ring2);
	// a.setRing(ring3);
	// System.out.println(a.fieldState);
	// System.out.println(a.isWinner());
	// }
	public void clear() {
		this.fieldState.clear();
		this.initfieldState();
	}
}
