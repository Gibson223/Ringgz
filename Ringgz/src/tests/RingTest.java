package tests;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;
import model.*;

class RingTest {

	@Test
	void constructorTest() {
		Ring ring1 = new Ring();
		Ring ring2 = new Ring(Color.BLUE,Tier.LARGE);
		assertEquals(ring1.getColor(),Color.INIT);
		assertEquals(ring1.getTier(),Tier.INIT);
		assertEquals(ring2.getColor(),Color.BLUE);
		assertEquals(ring2.getTier(),Tier.LARGE);
	}
	
	@Test
	void colorAndTierTest() {
		Ring ring1 = new Ring();
		ring1.setColor(Color.BLUE);
		ring1.setTier(Tier.LARGE);
		assertTrue(ring1.getColor() == Color.BLUE);
		assertTrue(ring1.getTier() == Tier.LARGE);
	}
	
	@Test
	void isRingTest() {
		assertTrue(Ring.isRing(Tier.BASE));
		assertTrue(Ring.isRing(Tier.LARGEST));
		assertTrue(Ring.isRing(Tier.LARGE));
		assertTrue(Ring.isRing(Tier.MEDIUM));
		assertTrue(Ring.isRing(Tier.SMALL));
	}
	
	@Test
	void equalsTest() {
		Ring ring1 = new Ring(Color.BLUE,Tier.LARGE);
		Ring ring2 = new Ring(Color.BLUE,Tier.LARGE);
		assertTrue(ring1.equals(ring2));
	}
	
	@Test
	void toStringTest() {
		Ring ring1 = new Ring(Color.BLUE,Tier.LARGE);
		assertEquals(ring1.toString(),"b");
	}

}
