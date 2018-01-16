
public class Board {
    public static final int DIM = 5;
    private static final String[] NUMBERING = {"1 | 2 | 3 | 4 | 5", "6 | 7 | 8 | 9 | 10", "11 | 12 | 13 | 14 | 15", "16 | 17 | 18 | 19 | 20", "21 | 22 | 23 | 24 | 25"};
    private static final String LINE0 = NUMBERING[0];
    private static final String LINE1 = NUMBERING[1];
    private static final String LINE2 = NUMBERING[2];
    private static final String LINE3 = NUMBERING[3];
    private static final String LINE4 = NUMBERING[4];
//    private static final String[] LINES = NUMBERING[];
    private static final String DELIM = "     ";

    /**
     * The DIM by DIM fields of the Ringgz student. See NUMBERING for the
     * coding of the fields.
     */
    //@ private invariant fields.length == DIM*DIM;
    private Field[] fields;

    // -- Constructors -----------------------------------------------

    /**
     * Creates an empty Board.
     */
    //@ ensures TODO;
    public Board() {
    	fields = new Field[DIM * DIM];
    	reset();
    	//a
    }

    /**
     * Creates a deep copy of the board.
     */
    //@ ensures \result != this;
    //TODO: Adapt this to copy all the rings from each field
    public Board deepCopy() {
        Board clone = new Board();
        for(int i = 0; i < fields.length; i++) {
        	clone.setField(i, fields[i]);
        }
        return clone;
    }

    /**
     * Calculates the index in the linear array of fields from a (row, col)
     * pair.
     * @return the index belonging to the (row,col)-field
     */
    //@ requires 0 <= row & row < DIM;
    //@ requires 0 <= col & col < DIM;
    /*@pure*/
    public int index(int row, int col) {
        return row*DIM + col;
    }

    /**
     * Returns true if ix is a valid index of a field on the student.
     * @return true if 0 <= index < DIM*DIM
     */
    //@ ensures \result == (0 <= index && index < DIM * DIM);
    /*@pure*/
    public boolean isField(int index) {
        return (index >= 0 && index < DIM * DIM);
    }

    /**
     * Returns true of the (row,col) pair refers to a valid field on the student.
     *
     * @return true if 0 <= row < DIM && 0 <= col < DIM
     */
    //@ ensures \result == (0 <= row && row < DIM && 0 <= col && col < DIM);
    /*@pure*/
    public boolean isField(int row, int col) {
        return (0 <= row && row < DIM && 0 <= col && col < DIM);
    }
    
    /**
     * Returns the content of the field i.
     *
     * @param i
     *            the number of the field (see NUMBERING)
     * @return the mark on the field
     */
    //@ requires this.isField(i);
    //@ ensures \result == Mark.EMPTY || \result == Mark.XX || \result == Mark.OO;
    /*@pure*/
    public Field getField(int i) {
        return fields[i];
    }

    /**
     * Returns the content of the field referred to by the (row,col) pair.
     *
     * @param row
     *            the row of the field
     * @param col
     *            the column of the field
     * @return the mark on the field
     */
    //@ requires this.isField(row,col);
    //@ ensures \result == Mark.EMPTY || \result == Mark.XX || \result == Mark.OO;
    /*@pure*/
    public Field getField(int row, int col) {
        return getField(index(row, col));
    }

    //RETURNS TRUE IF A CERTAIN RING CAN BE PLACED IN A CERTAIN FIELD
    //@ requires this.isField(i);
    //@ ensures TODO;
    /*@pure*/
    public boolean isAvailableField(int field, Ring RingType) {
        return true; //TODO (VERY IMPORTANT)
    }

    //RETURNS TRUE IF A CERTAIN RING CAN BE PLACED IN A CERTAIN FIELD
    //@ requires this.isField(row,col);
    //@ ensures TODO;
    /*@pure*/
    public boolean isAvailableField(int row, int col, Ring.RingType choice) {
        return isAvailableField(index(row, col));
    }
    
    //RETURNS TRUE IF A CERTAIN FIELD IS EMPTY
    //@ requires this.isField(i);
    //@ ensures TODO;
    /*@pure*/
    public boolean isEmptyField(int i) {
        return i.FieldState == FieldState.EMPTY;
    }

    //RETURNS TRUE IF A CERTAIN FIELD IS EMPTY
    //@ requires this.isField(row,col);
    //@ ensures TODO;
    /*@pure*/
    public boolean isEmptyField(int row, int col, Ring.RingType choice) {
        return isEmptyField(index(row, col));
    }


    //CHECKS IF BOARD IS FULL
    //@ ensures TODO (hint: for loop);
    /*@pure*/
    public boolean isFull() {
        for(int i = 0; i < fields.length; i++) {
        	if(getField(i) == Color.AVAILABLE) {
        		return false;
        	}
        }
        return true;
    }
    
    //RETURN WHETHER OR NOT THE SELECTED FIELD IS ADJACENT TO A FIELD WITH A CERTAIN COLOR RING IN IT
  	public boolean proximityCheck(int field, Color color) {
  		return (FieldHas((field - 4),color)) == true || FieldHas((field - 1),color)) == true || FieldHas((field + 1),color)) == true || FieldHas((field + 4),color)) == true); 	
  	    }
  	
  	public boolean FieldHas(int field, Color color) {
  		return; //THIS HAS TO RETURN IF A FIELD HAS A CERTAIN COLOR RING IN IT
  	}

    //RETURNS TRUE WHEN THE GAME ENDS (I.E. WHEN THE BOARD IS FULL)
    //@ ensures \result == this.isFull();
    /*@pure*/
    public boolean gameOver() {
        return (isFull());
    }

    //I THOUGHT ABOUT USING THIS A GUIDE FOR MAKING A CHECKER FOR A COMPLETE FIELD
    /*@ pure */
    public boolean hasWonField(int field, Color color) {
    	for(int r = 0; r < DIM; r++) {
//			boolean hasRow = true;
//			for(int c = 0; c < DIM; c++) {
//				if(getField(c + r*DIM) != m) {
//					hasRow = false;
//					break;
//				}
//	    	}
//			if(hasRow) {
//				return true;
//			}
//		}
//	    return false;
//	}

    /**
     * Checks if a player has won.
     *
     * @param player
     *            the player of interest
     * @return true if the player has won
     */
    //@requires TODO;
    //@ ensures TODO;
    /*@ pure */
    public boolean isWinner(Player player) {
        //TODO: conditions for winning
    }
    
    //TODO: this is the original form TTT, must be adapted
    public String toString() {
        String s = "";
        for (int i = 0; i < DIM; i++) {
            String row = "";
            for (int j = 0; j < DIM; j++) {
                row = row + " " + getField(i, j).toString() + " ";
                if (j < DIM - 1) {
                    row = row + "|";
                }
            }
            s = s + row + DELIM + NUMBERING[i * 2];
            if (i < DIM - 1) {
                s = s + "\n" + LINE + DELIM + NUMBERING[i * 2 + 1] + "\n";
            }
        }
        return s;
    }

    //RESETS THE BOARD
    //@ ensures TODO
    public void reset() {
    	for(int i = 0; i < fields.length; i++) {
    		setField(i,Color.NULL,Ring.RingType.NULL);
    	}
    }

    //@ requires this.isField(i);
    //@ ensures TODO;
    //PUTS THE DESIRED RING IN THE DESIRED FIELD
    public void setField(int i, Color c, Ring.RingType r) {
    	//TODO
    }
    
    //@ requires this.isField(row,col);
    //@ ensures this.getField(row,col) == m;
    public void setField(int row, int col, Color c, Ring.RingType r) {
    	setField(index(row, col), c, r);
    }
}
