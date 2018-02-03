package model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Observable;

import controller.RinggzException;

public class Field extends Observable {
	public int FieldNumber;

	// @requires this != null;
	// @ensures this.hasBase();
	public void placeBase() {
		this.fieldState.clear();
		this.fieldState.add(new Ring(Color.BLUE, Tier.SMALLEST));
		this.fieldState.add(new Ring(Color.GREEN, Tier.SMALL));
		this.fieldState.add(new Ring(Color.RED, Tier.MEDIUM));
		this.fieldState.add(new Ring(Color.YELLOW, Tier.LARGE));
		setChanged();
		notifyObservers("ring placed");
	}

	public Field() {
		this.initfieldState();
	}

	public void initfieldState() {
		fieldState.add(new Ring(Color.INIT, Tier.SMALLEST));
		fieldState.add(new Ring(Color.INIT, Tier.SMALL));
		fieldState.add(new Ring(Color.INIT, Tier.MEDIUM));
		fieldState.add(new Ring(Color.INIT, Tier.LARGE));
	}

	// small to large;
	// 1 = small
	// 4 = large;
	private List<Ring> fieldState = new ArrayList<>();

	// @requires this != null;
	// @pure
	public List<Ring> getFieldState() {
		return fieldState;
	}

	/**
	 * Checks whether or not a field has a certain color ring.
	 *
	 * @param color
	 *            the color in question
	 * @return true if the the field has that color in it, false otherwise.
	 */
	// @requires (color == Color.BLUE || color == Color.YELLOW || color == Color.RED
	// ||
	// color == Color.GREEN);
	// @pure
	public boolean hasColor(Color color) {
		for (Ring ring : fieldState) {
			if (ring.getColor() == color) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Checks whether or not a field has a base.
	 *
	 * @return true if the field has a base in it, false otherwise.
	 */
	// @requires this != null;
	// @pure
	public boolean hasBase() {
		for (Ring ring : fieldState)
			if (ring.getTier() == Tier.BASE && ring.getColor() != Color.INIT) {
				return true;
			}
		return false;
	}

	/**
	 * Checks whether or not a field is full.
	 *
	 * @return true if the field is full, false otherwise.
	 */
	// @requires this != null;
	// @pure
	public boolean isFull() {
		if (this.hasBase()) {
			return true;
		}
		for (Ring ring : fieldState) {
			if (!ring.getTier().occupied() || ring.getColor() == Color.INIT) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Checks whether or not a certain ring tier is already present in a field.
	 *
	 * @param r
	 *            the ring whose tier we want to check
	 * @return true if the ring tier is allowed, false otherwise.
	 */
	// @requires this != null && r != null
	// @pure
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

	/**
	 * Sets a ring on the field.
	 *
	 * @param ring
	 *            the ring we want to place
	 * 
	 */
	// @requires ring != null;
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

	/**
	 * Checks who the winner of the field is.
	 *
	 * @return the color with the majority of rings in the field.
	 */
	// @ensures (/result == Color.BLUE || /result == Color.YELLOW || /result ==
	// Color.RED || /result == Color.GREEN);
	/* @pure */
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
		if (map.isEmpty()) {
			return null;
		}
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

	/**
	 * Checks what colors the field has.
	 *
	 * @return a list of the colors present in the field.
	 */
	// @requires this != null;
	// @pure
	public List<Color> getFieldColors() {
		List<Color> result = new ArrayList<>();
		for (Ring ring : this.getFieldState()) {
			result.add(ring.getColor());
		}
		return result;
	}

	/**
	 * Transforms the state of the field into a string readable by a human
	 *
	 * @return a string with the current situation of the field (ring distribution).
	 */
	// @requires this != null;
	// @pure
	public String toString() {
		if (this.fieldState.stream().allMatch(a -> a.getColor() == Color.INIT && this.FieldNumber < 10)) {
			return "--" + this.FieldNumber + "-";
		}
		if (this.fieldState.stream().allMatch(a -> a.getColor() == Color.INIT)) {
			return "-" + this.FieldNumber + "-";
		}
		if (this.hasBase() == true) {
			return "" + fieldState.get(3).getColor() + "BAS";
		}
		String result = "";
		for (Ring ring : this.fieldState) {
			result += ring.toString();
		}

		return result;
	}

	/**
	 * Clears the field.
	 */
	// @requires this != null;
	// @ensures \old(this) != this;
	public void clear() {
		this.fieldState.clear();
		this.initfieldState();
	}
}
