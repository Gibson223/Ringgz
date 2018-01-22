package model;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Board {
    public static final int DIM = 5;
//    private static final String[] LINES = NUMBERING[];
    private static final String DELIM = "     ";
    public static void main(String[] args) {
		Board board = new Board();
		board.setRing(1, new Ring(Color.BLUE, Tier.BASE));
	}

    /**
     * The DIM by DIM fields of the Ringgz student. See NUMBERING for the
     * coding of the fields.
     */
    //@ private invariant fields.length == DIM*DIM;
    private Field[] fields;
    Map<Field, List<Ring>> allFields = new HashMap<Field, List<Ring>>();

    // -- Constructors -----------------------------------------------

    /**
     * Creates an empty Board.
     */
    //@ ensures TODO;
    //fields are being created according to debug
    public Board() {
    	fields = new Field[DIM * DIM];
    	for (int i = 0; i < 25; i++) {
    		fields[i] = new Field();
    	}
//    	for (Field field : fields) {
//    	allFields.put(field, field.getFieldState());}
    }

    /**
     * Creates a deep copy of the board.
     */
    //@ ensures \result != this;
    //TODO: Adapt this to copy all the rings from each field
    public Board deepCopy() {
        Board clone = new Board();
        clone.fields = this.fields;
        return clone;
    }

    /**
     * Calculates the index in the linear array of fields from a (row, col)
     * pair.
     * @return the index belonging to the (row,col)-field
     */
    //@ requires 0 <= row & row < DIM;
    //@ requires 0 <= col & col < DIM;
    //this.isField(row, col) && (allFields.containsKey(this.getField(index(row,col)).FieldNumber == index(row, col))
    /*@pure*/
    public int index(int row, int col) {
    	if (this.isField(row, col)) {
    		return (row-1)*DIM + col;}
    	else {
    		System.out.println("this is not a valid index...");
    		return -1;
    	}
    }
    public int index(int i) {
    	if (this.isField(i)) {
    		return i;}
    	else {
    		System.out.println("this is not a valid index...");
    		return -1;
    	}
    }
    /**
     * Returns true if ix is a valid index of a field on the student.
     * @return true if 0 <= index < DIM*DIM
     */
    //@ ensures \result == (0 <= index && index < DIM * DIM);
    /*@pure*/
    public boolean isField(int index) {
        return (index >= 1 && index <= DIM * DIM);
    }

    /**
     * Returns true of the (row,col) pair refers to a valid field on the student.
     *
     * @return true if 0 <= row < DIM && 0 <= col < DIM
     */
    //@ ensures \result == (0 <= row && row < DIM && 0 <= col && col < DIM);
    /*@pure*/
    public boolean isField(int row, int col) {
        return (1 <= row && row <= DIM && 1 <= col && col <= DIM);
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
    public boolean isAllowed(int field, Ring ring) {
    	return getField(field).isAllowed(ring);
    }

    //RETURNS TRUE IF A CERTAIN RING CAN BE PLACED IN A CERTAIN FIELD
    //@ requires this.isField(row,col);
    //@ ensures TODO;
    /*@pure*/
    public boolean isAllowed(int row, int col, Ring ring) {
        return getField(row, col).isAllowed(ring);
    }
    public void setRing(int i, Ring ring) {
    	movecheck(ring.getColor());
    	getField(i).setRing(ring);
    }
    
    //RETURNS TRUE IF A CERTAIN FIELD IS EMPTY - IMPORTANT TO CHECK IF A PLAYER CAN PLACE A BASE
    //@ requires this.isField(i);
    //@ ensures TODO;
    /*@pure*/
    public boolean isEmptyField(int i) {
    	return !fields[i].isFull();
    }
    

    //RETURNS TRUE IF A CERTAIN FIELD IS EMPTY
    //@ requires this.isField(row,col);
    //@ ensures TODO;
    /*@pure*/
    public boolean isEmptyField(int row, int col, Tier choice) {
        return isEmptyField(index(row, col));
    }
    //do while loop in player which makes it easy to register first move
    public List<Field> moveCheck(Color color){
    	if  {
    		
    	}
    }

    //CHECKS IF BOARD IS FULL
    //@ ensures TODO (hint: for loop);
    /*@pure*/
    public boolean boardIsFull() {
    	for (Field field : fields) {
    		if (!field.isFull()) {
    			return false;
    		}
    	}
    	return true;
    }
    
    //RETURN WHETHER OR NOT THE SELECTED FIELD IS ADJACENT TO A FIELD WITH A CERTAIN COLOR RING IN IT
//  	public boolean proximityCheck(int field, Color color) {
//  		return (FieldHas((field - 4),color)) == true || FieldHas((field - 1),color)) == true || FieldHas((field + 1),color)) == true || FieldHas((field + 4),color)) == true); 	
//  	    }
//  	
  	public boolean FieldHasColor(int field, Color color) {
  		return getField(field).HasColor(color);
    	}

    //RETURNS TRUE WHEN THE GAME ENDS (I.E. WHEN THE BOARD IS FULL)
    //@ ensures \result == this.isFull();
    /*@pure*/
    public boolean gameOver() {
        return (this.boardIsFull());
    }

    //I THOUGHT ABOUT USING THIS A GUIDE FOR MAKING A CHECKER FOR A COMPLETE FIELD
    /*@ pure */
//    public boolean hasWonField(int field, Color color) {
//    	for(int r = 0; r < DIM; r++) {
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
//    public boolean isWinner(Player player) {
//        //TODO: conditions for winning
//    }
    
    //TODO: this is the original form TTT, must be adapted
//    public String toString() {
//        String s = "";
//        for (int i = 0; i < DIM; i++) {
//            String row = "";
//            for (int j = 0; j < DIM; j++) {
//                row = row + " " + getField(i, j).toString() + " ";
//                if (j < DIM - 1) {
//                    row = row + "|";
//                }
//            }
//            s = s + row + DELIM + NUMBERING[i * 2];
//            if (i < DIM - 1) {
//                s = s + "\n" + LINE + DELIM + NUMBERING[i * 2 + 1] + "\n";
//            }
//        }
//        return s;
//    }

    //RESETS THE BOARD
    //@ ensures TODO
    public void reset() {
    	for( Field field : fields) {
    		field.clear();
    	}
    }
}
