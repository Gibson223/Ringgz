package tests;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;
import model.*;
public class TierTest {
	Tier small = Tier.BASE;
	Tier medium = Tier.MEDIUM;
	Tier large = Tier.LARGE;
	Tier largest = Tier.LARGEST;
	Tier base = Tier.BASE;
	Tier init = Tier.INIT;
	@Before
	public void setUp() throws Exception {
	}
	@Test
	public void testToChar() {
		assertTrue(Tier.toTier(1) == Tier.SMALL);
		assertTrue(Tier.toTier(2) == Tier.MEDIUM);
		assertTrue(Tier.toTier(3) == Tier.LARGE);
		assertTrue(Tier.toTier(4) == Tier.LARGEST);
		assertTrue(Tier.toTier(5) == Tier.BASE);
		assertTrue(Tier.toTier(10) == null);
	}
	@Test
	public void testOccupied() {
		assertTrue(small.occupied());
		assertTrue(medium.occupied());
		assertTrue(large.occupied());
		assertTrue(largest.occupied());
		assertTrue(base.occupied());
		assertFalse(init.occupied());
		
	}
}
