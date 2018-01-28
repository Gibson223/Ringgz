package tests;

import static org.junit.Assert.*;
import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.Before;
import org.junit.Test;

import model.Color;
import model.Field;
import model.Ring;
import model.Tier;

public class FieldTest {

	private Field field;
	private Field field2;

	@Before
	public void setUp() throws Exception {
		field = new Field();
		field2 = new Field();
	}

	@Test
	public void testDefault() {
//		assertTrue(field.FieldNumber == 1);
//		assertTrue(field2.FieldNumber == 2);
		assertTrue(field.getFieldState().size() == 4);
		assertTrue(field.getFieldState().get(1).getColor() == Color.INIT && 
				field.getFieldState().get(1).getTier() == Tier.MEDIUM);
		assertTrue(field.getFieldState().get(2).getColor() == Color.INIT && 
				field.getFieldState().get(2).getTier() == Tier.LARGE);
		assertTrue(field.getFieldState().get(3).getColor() == Color.INIT && 
				field.getFieldState().get(3).getTier() == Tier.LARGEST);
		assertTrue(field.getFieldState().get(0).getColor() == Color.INIT && 
				field.getFieldState().get(0).getTier() == Tier.SMALL);
	}
	@Test
	public void testColor() {
		assertFalse(field.HasColor(Color.BLUE));
		assertFalse(field.HasColor(Color.RED));
		assertFalse(field.HasColor(Color.YELLOW));
		assertFalse(field.HasColor(Color.GREEN));
		assertTrue(field.HasColor(Color.INIT));
		assertEquals(field.HasColor(Color.BLUE), false);
	}

	@Test
	public void testPlaceBase() {
		field.placeBase();
		assertEquals(field.getFieldState().get(0).getColor(), Color.BLUE);
		assertEquals(field.getFieldState().get(1).getColor(), Color.GREEN);
		assertEquals(field.getFieldState().get(2).getColor(), Color.RED);
		assertEquals(field.getFieldState().get(3).getColor(), Color.YELLOW);
		assertEquals(field.getFieldState().get(0).getTier(), Tier.SMALL);
		assertEquals(field.getFieldState().get(1).getTier(), Tier.MEDIUM);
		assertEquals(field.getFieldState().get(2).getTier(), Tier.LARGE);
		assertEquals(field.getFieldState().get(3).getTier(), Tier.LARGEST);
	}

	@Test
	public void testClear() {
		field.clear();
		assertEquals(field.getFieldState().get(0).getColor(), Color.INIT);
		assertEquals(field.getFieldState().get(1).getColor(), Color.INIT);
		assertEquals(field.getFieldState().get(2).getColor(), Color.INIT);
		assertEquals(field.getFieldState().get(3).getColor(), Color.INIT);
		assertEquals(field.getFieldState().get(0).getTier(), Tier.SMALL);
		assertEquals(field.getFieldState().get(1).getTier(), Tier.MEDIUM);
		assertEquals(field.getFieldState().get(2).getTier(), Tier.LARGE);
		assertEquals(field.getFieldState().get(3).getTier(), Tier.LARGEST);
	}
	@Test
	public void testHasBase() {
		assertEquals(field.HasBase(), false);
		field.getFieldState().set(0, (new Ring(Color.BLUE, Tier.BASE)));
		assertEquals(field.HasBase(),true);
		field.getFieldState().set(0, (new Ring(Color.INIT, Tier.BASE)));
		assertEquals(field.HasBase(),false);
	}
	@Test
	public void testisFull() {
	field.clear();
//	field.getFieldState().stream().forEach(a -> System.out.println("" + a.getColor() + a.getTier()));
//	assertEquals(field.isFull(), false);
	field.getFieldState().set(0, (new Ring(Color.BLUE, Tier.BASE)));
	assertEquals(field.HasBase(),true);
	field.getFieldState().set(0, (new Ring(Color.INIT, Tier.BASE)));
	assertEquals(field.isFull(), false);
//	field.getFieldState().set(0, new Ring(Color.YELLOW, Tier.LARGEST));
//	field.getFieldState().set(0, new Ring(Color.BLUE, Tier.LARGE));
//	field.getFieldState().set(0, new Ring(Color.GREEN, Tier.MEDIUM));
//	field.getFieldState().set(0, new Ring(Color.RED, Tier.SMALL));
//	assertEquals(field.isFull(), true);
	}
}
