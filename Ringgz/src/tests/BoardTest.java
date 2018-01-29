package tests;
import model.*;
import controller.*;
import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class BoardTest {
	Board board;
	
	@BeforeEach
	void setUp() {
		board = new Board();
	}

	@Test
	void indexTest() {
		assertTrue(board.index(1,1) == 1);
		assertTrue(board.index(5,5) == 25);
		assertTrue(board.index(65,24) == -1);
		assertTrue(board.index(1) == 1);
		assertTrue(board.index(25) == 25);
		assertTrue(board.index(336) == -1);
	}
	
	@Test
	void isFieldTest() {
		assertTrue(board.isField(1,1));
		assertTrue(board.isField(5,5));
		assertFalse(board.isField(5,6));
		assertTrue(board.isField(1));
		assertTrue(board.isField(25));
		assertFalse(board.isField(26));
	}
	
	@Test
	void getFieldTest() throws RinggzException{
		assertEquals(board.getField(1), board.fields[0]);
		assertEquals(board.getField(25), board.fields[24]);
		assertEquals(board.getField(1,1), board.fields[0]);
		assertEquals(board.getField(5,5), board.fields[24]);		
	}
	
	@Test
	void adjacentFieldTest() throws RinggzException{
		System.out.println(board.adjacentFields(1));
		assertEquals(board.adjacentFields(1),Arrays.asList(board.getField(6),board.getField(2)));
	}
	
	@Test
	void proximityCheckTest() throws RinggzException {
		Ring ring1 = new Ring(Color.BLUE, Tier.SMALL);
		board.setRing(1, ring1);
		assertTrue(board.proximityCheck(6,Color.BLUE));
		assertTrue(board.proximityCheck(2,Color.BLUE));
	}
	
	@Test
	void isAllowedTest() throws RinggzException {
		Ring ring1 = new Ring(Color.BLUE, Tier.SMALL);
		board.setRing(1, ring1);
		assertFalse(board.isAllowed(1,1,ring1));
		assertFalse(board.isAllowed(1,ring1));
		assertTrue(board.isAllowed(1,2,ring1));
		assertTrue(board.isAllowed(2,ring1));
	}
	
	@Test
	void adjacentHasBaseTest() throws RinggzException {
		Ring ring1 = new Ring(Color.BLUE, Tier.BASE);
		board.setRing(1, ring1);
		assertTrue(board.adjacentHasBase(2, ring1));
	}
	
	@Test
	void isEmptyFieldTest() throws RinggzException{
		board.reset();
		assertTrue(board.isEmptyField(1));
		assertTrue(board.isEmptyField(25));
		assertTrue(board.isEmptyField(1,1,Tier.LARGE));
	}
	
	@Test
	void resetTest() throws RinggzException {
		Board b = new Board();
		Ring ring = new Ring();
		ring.setColor(Color.RED);
		ring.setTier(Tier.BASE);
		b.setRing(1, ring);
		b.setRing(25, ring);
		b.reset();
		assertEquals(b.getField(1).toString(),"--1-");
		assertEquals(b.getField(25).toString(),"-25-");
	}
	
	@Test
	void specialBaseTest() throws RinggzException {
		Board board = new Board();
		board.specialBase(1);
		System.out.println(board.getField(1).toString());
		assertEquals(board.getField(1).toString(), "bgry");
	}
	
	@Test
	//Fills all fields with blue rings and checks who has the majority of won fields
	void isWinnerTest() throws RinggzException{
		board.reset();
		Ring ring1 = new Ring(Color.BLUE, Tier.SMALL);
		Ring ring2 = new Ring(Color.BLUE, Tier.MEDIUM);
		Ring ring3 = new Ring(Color.BLUE, Tier.LARGE);
		Ring ring4 = new Ring(Color.BLUE, Tier.LARGEST);
		for (Field field : board.fields) {
			board.setRing(field.FieldNumber, ring1);	
			board.setRing(field.FieldNumber, ring2);
			board.setRing(field.FieldNumber, ring3);
			board.setRing(field.FieldNumber, ring4);
		}
		assertTrue(board.isWinner() == Color.BLUE);
	}
	
	@Test
	void boardIsFullTest() throws RinggzException {
		board.reset();
		Ring ring1 = new Ring(Color.BLUE, Tier.SMALL);
		Ring ring2 = new Ring(Color.BLUE, Tier.MEDIUM);
		Ring ring3 = new Ring(Color.BLUE, Tier.LARGE);
		Ring ring4 = new Ring(Color.BLUE, Tier.LARGEST);
		for (Field field : board.fields) {
			board.setRing(field.FieldNumber, ring1);	
			board.setRing(field.FieldNumber, ring2);
			board.setRing(field.FieldNumber, ring3);
			board.setRing(field.FieldNumber, ring4);
		}
		assertTrue(board.boardIsFull());
	}
	
	@Test
	void gameOverTest() throws RinggzException {
		board.reset();
		Ring ring1 = new Ring(Color.BLUE, Tier.SMALL);
		Ring ring2 = new Ring(Color.BLUE, Tier.MEDIUM);
		Ring ring3 = new Ring(Color.BLUE, Tier.LARGE);
		Ring ring4 = new Ring(Color.BLUE, Tier.LARGEST);
		for (Field field : board.fields) {
			board.setRing(field.FieldNumber, ring1);	
			board.setRing(field.FieldNumber, ring2);
			board.setRing(field.FieldNumber, ring3);
			board.setRing(field.FieldNumber, ring4);
		}
		assertTrue(board.gameOver());
	}
	
	@Test
	void deepCopyTest() throws RinggzException {
		Board board = new Board();
		Ring ring1 = new Ring(Color.BLUE, Tier.SMALL);
		board.setRing(1, ring1);
		Board clone = board.deepCopy();
		assertEquals(clone.fields, board.fields);
	}
	
	@Test
	void FieldHasColorTest() throws RinggzException {
		Ring ring1 = new Ring(Color.BLUE, Tier.SMALL);
		board.setRing(1, ring1);
		assertTrue(board.FieldHasColor(1,Color.BLUE));
	}
	
}
