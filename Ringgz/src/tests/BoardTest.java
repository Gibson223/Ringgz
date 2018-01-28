package tests;
import model.*;
import controller.*;
import java.util.ArrayList;

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
	
//	@Test
//	void adjacentFieldTest() {
//		System.out.println(board.adjacentFields(1));
//		assertEquals(board.adjacentFields(1),(ArrayList) [-81-, -77-]);
//	}
	
	@Test
	void gameOverTest() {
		assertFalse(!board.boardIsFull());
	}
	
	@Test
	void resetTest() throws RinggzException{
		board.reset();
		Ring ring = new Ring();
		board.setRing(1, ring);
		board.setRing(25, ring);
		board.reset();
		assertEquals(board.getField(1).toString(),"-101-");
		assertEquals(board.getField(25).toString(),"-125-");
	}
	
	
}
