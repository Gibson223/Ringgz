package model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import controller.RinggzException;
import view.TUI;

public class Board {
	public static final int DIM = 5;
	public boolean firstMove = true;
	public final List<Integer> middle9 = Arrays.asList(7, 8, 9, 12, 13, 14, 17, 18, 19);

	public void specialBase(int i) throws RinggzException {
		this.getField(i).placeBase();
	}

	/**
	 * The DIM by DIM fields of the Ringgz student. See NUMBERING for the coding of
	 * the fields.
	 */
	// @ private invariant fields.length == DIM*DIM;
	public Field[] fields;
	// Map<Field, List<Ring>> allFields = new HashMap<Field, List<Ring>>();
	public final TUI tui;

	// -- Constructors -----------------------------------------------

	/**
	 * Creates an empty Board.
	 */
	// @ ensures TODO;
	// fields are being created according to debug
	public Board(TUI tui) {
		this.tui = tui;
		fields = new Field[DIM * DIM];
		for (int i = 0; i < 25; i++) {
			fields[i] = new Field();
			fields[i].FieldNumber = i + 1;
			firstMove = true;
		}
		// for (Field field : fields) {
		// allFields.put(field, field.getFieldState());}
	}

	/**
	 * Calculates the index in the linear array of fields from a (row, col) pair.
	 * 
	 * @return the index belonging to the (row,col)-field
	 */
	// @ requires 0 <= row & row < DIM;
	// @ requires 0 <= col & col < DIM;
	// this.isField(row, col) &&
	// (allFields.containsKey(this.getField(index(row,col)).FieldNumber ==
	// index(row, col))
	/* @pure */
	public int index(int row, int col) {
		if (this.isField(row, col)) {
			return (row - 1) * DIM + col;
		} else {
			System.out.println("this is not a valid index...");
			return -1;
		}
	}

	// @ requires 0 <= i & col < (DIM*DIM);
	// this.isField(i) &&
	// (allFields.containsKey(this.getField(i).FieldNumber == i
	/* @pure */
	public int index(int i) {
		if (this.isField(i)) {
			return i;
		} else {
			System.out.println("this is not a valid index...");
			return -1;
		}
	}

	/**
	 * Returns true if ix is a valid index of a field on the student.
	 * 
	 * @return true if 0 <= index < DIM*DIM
	 */
	// @ ensures \result == (0 <= index && index < DIM * DIM);
	/* @pure */
	public boolean isField(int index) {
		return index >= 1 && index <= DIM * DIM;
	}

	/**
	 * Returns true of the (row,col) pair refers to a valid field on the student.
	 *
	 * @return true if 0 <= row < DIM && 0 <= col < DIM
	 */
	// @ ensures \result == (0 <= row && row < DIM && 0 <= col && col < DIM);
	/* @pure */
	public boolean isField(int row, int col) {
		return 1 <= row && row <= DIM && 1 <= col && col <= DIM;
	}

	/**
	 * Returns the content of the field i.
	 *
	 * @param i
	 *            the number of the field (see NUMBERING)
	 * @return the mark on the field
	 * @throws RinggzException
	 */
	// @ requires this.isField(i);
	/* @pure */
	public Field getField(int i) throws RinggzException {
		if (this.isField(i)) {
			return fields[i - 1];
		} else {
			throw new RinggzException("Not a valid field, so cannot get it....");
		}
	}

	/**
	 * Returns the content of the field referred to by the (row,col) pair.
	 *
	 * @param row
	 *            the row of the field
	 * @param col
	 *            the column of the field
	 * @return the mark on the field
	 * @throws RinggzException
	 */
	// @ requires this.isField(row,col);
	/* @pure */
	public Field getField(int row, int col) throws RinggzException {
		return getField(index(row, col));
	}

	// RETURNS TRUE IF AN ADJACENT FIELD HAS A BASE
	// @requires this.isField(i);
	// @pure
	public boolean adjacentHasBase(int field, Ring ring) {
		if (ring.getTier() == Tier.BASE) {
			for (Field fieldforbase : this.adjacentFields(field)) {
				if (fieldforbase.hasBase()
						&&
						(fieldforbase.getFieldState().
								stream().anyMatch(a -> a.getColor() == ring.getColor()))) {
					return true;
				}
			}
		}
		return false;
	}

	// RETURNS TRUE IF A CERTAIN RING CAN BE PLACED IN A CERTAIN FIELD
	// @ requires this.isField(i);
	/* @pure */
	public boolean isAllowed(int field, Ring ring) throws RinggzException {
		return getField(field).isAllowed(ring) && !this.adjacentHasBase(field, ring);
	}

	// RETURNS TRUE IF A CERTAIN RING CAN BE PLACED IN A CERTAIN FIELD
	// @ requires this.isField(row,col);
	/* @pure */
	public boolean isAllowed(int row, int col, Ring ring) throws RinggzException {
		return this.isAllowed(index(row, col), ring);

	}

	public void setRing(int i, Ring ring) throws RinggzException {
		getField(i).setRing(ring);
	}

	// RETURNS TRUE IF A CERTAIN FIELD IS EMPTY - IMPORTANT TO CHECK IF A PLAYER CAN
	// PLACE A BASE
	// @ requires this.isField(i);
	/* @pure */
	public boolean isEmptyField(int i) throws RinggzException {
		return !this.getField(i).isFull();
	}

	// RETURNS TRUE IF A CERTAIN FIELD IS EMPTY
	// @ requires this.isField(row,col);
	/* @pure */
	public boolean isEmptyField(int row, int col, Tier choice) throws RinggzException {
		return isEmptyField(index(row, col));
	}
	// do while loop in player which makes it easy to register first move

	// CHECKS IF BOARD IS FULL
	/* @pure */
	public boolean boardIsFull() {
		for (Field field : fields) {
			if (!field.isFull()) {
				return false;
			}
		}
		return true;
	}

	private List<Integer> left = Arrays.asList(1, 6, 11, 16, 21);
	private List<Integer> right = Arrays.asList(5, 10, 15, 20, 25);

	// @returns List<Field> of adjacent fields
	// @requires this.isField(field);
	/* @pure */
	public List<Field> adjacentFields(int field) {
		List<Field> result = new ArrayList<>();
		if (this.isField(field + DIM)) {
			try {
				result.add(this.getField(field + DIM));
			} catch (RinggzException e) {
				/* do nothing */
			}
		}
		
		if (this.isField(field - DIM)) {
			try {
				result.add(this.getField(field - DIM));
			} catch (RinggzException f) {
				/* do nothing */
			}
		}

		if (!left.contains(field)) {
			try {
				result.add(this.getField(field - 1));
			} catch (RinggzException g) {
				/* do nothing */
			}
		}

		if (!right.contains(field)) {
			try {
				result.add(this.getField(field + 1));
			} catch (RinggzException h) {
				/* do nothing */
			}
		}

		return result;
	}

	// @requires this.isField(f)
	// @requires (c == Color.BLUE || c == Color.YELLOW || c == Color.RED || c ==
	// Color.GREEN);
	/* @pure */
	public boolean proximityCheck(int f, Color c) {
		for (Field field : this.adjacentFields(f)) {
			for (Ring ring : field.getFieldState()) {
				if (ring.getColor() == c) {
					return true;
				}
			}
		}
		return false;
	}

	// @requires this.isField(field)
	// @requires (c == Color.BLUE || c == Color.YELLOW || c == Color.RED || c ==
	// Color.GREEN);
	/* @pure */
	public boolean fieldHasColor(int field, Color color) throws RinggzException {
		return getField(field).hasColor(color);
	}

	// RETURNS TRUE WHEN THE GAME ENDS (I.E. WHEN THE BOARD IS FULL)
	// @ ensures \result == this.isFull();
	/* @pure */
	public boolean gameOver() {
		return this.boardIsFull();
	}

	// @ensures (/result == Color.BLUE || /result == Color.YELLOW || /result ==
	// Color.RED || /result == Color.GREEN);
	/* @pure */
	public Color isWinner() {
		Map<Color, Integer> result = new HashMap<>();
		for (Color c : Color.values()) {
			result.put(c, 0);
		}
		for (Field field : fields) {
			result.put(field.isWinner(), result.get(field.isWinner()) + 1);
		}
		result.remove(null);
		System.out.println(result);
		Integer highest = java.util.Collections.max(result.values());
		if (java.util.Collections.frequency(result.values(), highest) == 1) {
			for (Map.Entry<Color, Integer> c : result.entrySet()) {
				if (c.getValue() == highest) {
					return c.getKey();
				}
			}
		}
		return null;
	}

	// RESETS THE BOARD
	// @ensures this.fields() != \old(this).fields();
	public void reset() {
		for (Field field : fields) {
			field.clear();
		}
	}
}
