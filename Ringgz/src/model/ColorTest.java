package model;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

class ColorTest {
	
	@Test
	void toColorTest() {
		assertEquals(Color.YELLOW, Color.toColor('y'));
		assertEquals(Color.BLUE, Color.toColor('b'));
		assertEquals(Color.GREEN, Color.toColor('g'));
		assertEquals(Color.RED, Color.toColor('r'));
	}
	
	@Test
	void toStringTest() {
		assertEquals(Color.YELLOW.toString(), "y");
		assertEquals(Color.BLUE.toString(), "b");
		assertEquals(Color.GREEN.toString(), "g");
		assertEquals(Color.RED.toString(), "r");
	}
	
	@Test
	void nextTest() {
		assertEquals(Color.RED.next(), Color.YELLOW);
		assertEquals(Color.YELLOW.next(), Color.GREEN);
		assertEquals(Color.GREEN.next(), Color.BLUE);
		assertEquals(Color.BLUE.next(), Color.RED);
	}

}
