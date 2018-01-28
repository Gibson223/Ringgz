package tests;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;
import model.*;
public class TierTest {
	private Tier small ;
	private Tier medium;
	private Tier large ;
	private Tier largest ;
	private Tier base ;
	private Tier init ;
	@Before
	public void setUp() throws Exception {
		small = Tier.SMALL;
		medium = Tier.MEDIUM;
		large = Tier.LARGE;
		largest = Tier.LARGEST;
		base = Tier.BASE;
		init = Tier.INIT;
	}
	@Test
	public void testToChar() {
		assertTrue(Tier.toTier(1) == Tier.SMALL);
		assertTrue(Tier.toTier(2) == Tier.MEDIUM);
		assertTrue(Tier.toTier(3) == Tier.LARGE);
		assertTrue(Tier.toTier(4) == Tier.LARGEST);
		assertTrue(Tier.toTier(5) == Tier.BASE);
		assertTrue(Tier.toTier(10) == null);
		assertFalse(Tier.toTier(1) == Tier.INIT);
		assertFalse(Tier.toTier(2) == Tier.INIT);
		assertFalse(Tier.toTier(3) == Tier.INIT);
		assertFalse(Tier.toTier(4) == Tier.INIT);
		assertFalse(Tier.toTier(5) == Tier.INIT);
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
