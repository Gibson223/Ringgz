package tests;
import model.Color;
import model.Ring;

import static org.junit.Assert.assertTrue;


import org.junit.Before;
import org.junit.Test;

import model.RingList;

class RingListTest {
	private RingList a;
	@Before
	void setUp() throws Exception {
		RingList a = new RingList();
//		a.availableRings.stream().forEach(b -> System.out.println(" " + b.getColor() + b.getTier(), rings.);
		
	}

	@Test
	void test() {
		assertTrue(a.availableRings.size() == 60);
		assertTrue(a.availableRings.stream().filter(a -> a.getColor() ==Color.BLUE).count() == 15);
		assertTrue(a.availableRings.stream().filter(a -> a.getColor() ==Color.YELLOW).count() == 15);
		assertTrue(a.availableRings.stream().filter(a -> a.getColor() ==Color.RED).count() == 15);
		assertTrue(a.availableRings.stream().filter(a -> a.getColor() ==Color.GREEN).count() == 15);
	}
}
