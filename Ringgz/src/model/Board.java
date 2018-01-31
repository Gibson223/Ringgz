package model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import controller.RinggzException;
import view.TUI;

public class Board {
	public static int[] xy(int field) {
		field -= 1;
		int[] result = new int[2];
		if (field < 5) {
			result[1] = 0;
		} else if (field < 10) {
			result[1] = 1;
		} else if (field < 15) {
			result[1] = 2;
		} else if (field < 20) {
			result[1] = 3;
		} else if (field < 25) {
			result[1] = 4;
		}
		result[0] = ((field % (result[1] * 5)));
		return result;
	}

	public static final int DIM = 5;
	public boolean firstMove = true;
	public final List<Integer> middle9 = Arrays.asList(7, 8, 9, 12, 13, 14, 17, 18, 19);
	private final List<Integer> left = Arrays.asList(1, 6, 11, 16, 21);
	private final List<Integer> right = Arrays.asList(5, 10, 15, 20, 25);

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

	// -- Constructors -----------------------------------------------

	/**
	 * Creates an empty Board.
	 */
	// @ ensures TODO;
	// fields are being created according to debug
	public Board() {
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

	/**
	 * Checks that the inputed field number is a valid field.
	 *
	 * @param i
	 *            the field in question
	 * 
	 * @return i if the field is valid, -1 otherwise.
	 */
	// @ requires 0 <= i & i < (DIM*DIM);
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
	 * @return the field
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
	 * @return the field
	 * @throws RinggzException
	 */
	// @ requires this.isField(row,col);
	/* @pure */
	public Field getField(int row, int col) throws RinggzException {
		return getField(index(row, col));
	}

	/**
	 * Returns if a field has another field with a base adjacent to it.
	 *
	 * @param field
	 *            the field in question
	 * @param ring
	 *            the base
	 * @return true if there is a base in an adjacent field, false otherwise.
	 */
	// @requires this.isField(i);
	// @pure
	public boolean adjacentHasBase(int field, Ring ring) {
		if (ring.getTier() == Tier.BASE) {
			for (Field fieldforbase : this.adjacentFields(field)) {
				if (fieldforbase.hasBase()
						&& (fieldforbase.getFieldState().stream().anyMatch(a -> a.getColor() == ring.getColor()))) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Returns if a certain ring can be placed in a certain field.
	 *
	 * @param field
	 *            the field in question
	 * @param ring
	 *            the ring we want to test
	 * @return true if the ring can be placed in the field, flase otherwise.
	 * @throws RinggzException
	 */
	// @ requires this.isField(i);
	/* @pure */
	public boolean isAllowed(int field, Ring ring) throws RinggzException {
		return getField(field).isAllowed(ring) && !this.adjacentHasBase(field, ring);
	}

	/**
	 * Row and column adaptation of isAllowed(field,ring).
	 *
	 * @param row
	 *            the row of the field in question
	 * @param col
	 *            the column of the field in question
	 * @param ring
	 *            the ring we want to test
	 * @return true if the ring can be placed in the field, flase otherwise.
	 * @throws RinggzException
	 */
	// RETURNS TRUE IF A CERTAIN RING CAN BE PLACED IN A CERTAIN FIELD
	// @ requires this.isField(row,col);
	/* @pure */
	public boolean isAllowed(int row, int col, Ring ring) throws RinggzException {
		return this.isAllowed(index(row, col), ring);

	}

	/**
	 * Returns if a certain ring can be placed in a certain field.
	 *
	 * @param i
	 *            the field in question
	 * @param ring
	 *            the ring we want to place
	 * @return nothing (void).
	 * @throws RinggzException
	 */
	// @requires i.isField() && ring != null;
	// @ensures \old(board) != board;
	public void setRing(int i, Ring ring) throws RinggzException {
		getField(i).setRing(ring);
	}

	/**
	 * Returns if a certain field is empty.
	 *
	 * @param i
	 *            the field in question
	 * @return true if the field is empty, false otherwise.
	 * @throws RinggzException
	 */
	// @ requires this.isField(i);
	/* @pure */
	public boolean isEmptyField(int i) throws RinggzException {
		return !this.getField(i).isFull();
	}

	/**
	 * Row-column adaptation of isEmptyField(field).
	 *
	 * @param row
	 *            the row of the field in question
	 * @param col
	 *            the column of the field in question
	 * @param ring
	 *            the tier we want to test for emptiness
	 * @return true if the field is empty, false otherwise.
	 * @throws RinggzException
	 */
	// @ requires this.isField(row,col);
	/* @pure */
	public boolean isEmptyField(int row, int col, Tier choice) throws RinggzException {
		return isEmptyField(index(row, col));
	}

	/**
	 * Returns whether the board is full.
	 *
	 * @return true if the board is full, false otherwise.
	 */
	/* @pure */
	public boolean boardIsFull() {
		for (Field field : fields) {
			if (!field.isFull()) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Returns a list of the adjacent fields of a certain field.
	 *
	 * @param field
	 *            the field in question
	 * @return a list of fields that are adjacent to the field in the arguments.
	 */
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

	/**
	 * Returns whether there is a certain color in the adjacent fields of a certain
	 * field.
	 *
	 * @param field
	 *            the field in question
	 * @param c
	 *            the color we are looking for
	 * @return true if there is a ring with that color in the adjacent fields of the
	 *         specified field.
	 */
	// @requires this.isField(f)
	// @requires (c == Color.BLUE || c == Color.YELLOW || c == Color.RED || c ==
	// Color.GREEN);
	/* @pure */
	public boolean proximityCheck(int field, Color c) {
		for (Field i : this.adjacentFields(field)) {
			for (Ring ring : i.getFieldState()) {
				if (ring.getColor() == c) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Returns whether there is a certain color in the adjacent fields of a certain
	 * field.
	 *
	 * @param field
	 *            the field in question
	 * @param c
	 *            the color we are looking for
	 * @return true if there is a ring with that color in the adjacent fields of the
	 *         specified field.
	 */
	// @requires this.isField(field)
	// @requires (c == Color.BLUE || c == Color.YELLOW || c == Color.RED || c ==
	// Color.GREEN);
	/* @pure */
	public boolean fieldHasColor(int field, Color color) throws RinggzException {
		return getField(field).hasColor(color);
	}

	/**
	 * Returns whether the game is over or not.
	 * 
	 * @return true if the game is over, false otherwise.
	 */
	// @ ensures \result == this.boardIsFull();
	/* @pure */
	public boolean gameOver() {
		return this.boardIsFull();
	}

	/**
	 * Returns the color who has won.
	 *
	 * @return the color with the most won fields.
	 * 
	 */
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

	/**
	 * Resets the board.
	 */
	// @ensures this.fields() != \old(this).fields();
	public void reset() {
		for (Field field : fields) {
			field.clear();
		}
	}
}
