package tests;

import static org.junit.Assert.*;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

import java.util.ArrayList;
import java.util.Arrays;

import org.junit.Before;
import org.junit.Test;

import controller.RinggzException;
import model.Board;
import model.Color;
import model.Field;
import model.Ring;
import model.Tier;
import view.TUI;

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
	field.getFieldState().set(0, (new Ring(Color.BLUE, Tier.BASE)));
	assertEquals(field.HasBase(),true);
	field.getFieldState().set(0, (new Ring(Color.INIT, Tier.BASE)));
	assertEquals(field.isFull(), false); 
	field.getFieldState().set(0, (new Ring(Color.BLUE, Tier.SMALL)));
	field.getFieldState().set(1, (new Ring(Color.INIT, Tier.MEDIUM)));
	assertEquals(field.isFull(), false);
	field.getFieldState().set(0, (new Ring(Color.BLUE, Tier.SMALL)));
	field.getFieldState().set(1, (new Ring(Color.GREEN, Tier.MEDIUM)));
	field.getFieldState().set(2, (new Ring(Color.GREEN, Tier.LARGE)));
	field.getFieldState().set(3, (new Ring(Color.GREEN, Tier.LARGEST)));
	assertEquals(field.isFull(), true);
	}
	@Test
	public void testisAllowed() {
		field.getFieldState().set(0, (new Ring(Color.BLUE, Tier.SMALL)));
		field.getFieldState().set(1, (new Ring(Color.GREEN, Tier.MEDIUM)));
		field.getFieldState().set(2, (new Ring(Color.GREEN, Tier.LARGE)));
		field.getFieldState().set(3, (new Ring(Color.GREEN, Tier.LARGEST)));
		assertFalse(field.isAllowed(new Ring(Color.BLUE, Tier.SMALL)));
		field.getFieldState().set(0, (new Ring(Color.INIT, Tier.SMALL)));
		assertTrue(field.isAllowed(new Ring(Color.BLUE, Tier.SMALL))); 
		assertFalse(field.isAllowed(new Ring(Color.GREEN, Tier.MEDIUM)));		
	}
	@Test
	public void testsetRing() {
		field.setRing(new Ring(Color.GREEN, Tier.MEDIUM));
		assertEquals(field.getFieldState().get(1).getColor(), Color.GREEN);
		assertEquals(field.getFieldState().get(1).getTier(),Tier.MEDIUM); 
		field.setRing(new Ring(Color.GREEN, Tier.BASE));
		assertEquals(field.getFieldState().get(3).getColor(), Color.GREEN);
		assertEquals(field.getFieldState().get(3).getTier(),Tier.BASE); 
		field.setRing(new Ring(Color.BLUE, Tier.MEDIUM));
		assertEquals(field.getFieldState().get(3).getColor(), Color.GREEN);
	}
	@Test
	public void testisWinner() {
		assertNull(field.isWinner());
		field.setRing(new Ring(Color.GREEN, Tier.MEDIUM));
		assertEquals(field.isWinner(), Color.GREEN);
		field.setRing(new Ring(Color.YELLOW, Tier.SMALL));
		assertNull(field.isWinner());
		field.setRing(new Ring(Color.YELLOW, Tier.LARGE));
		assertEquals(field.isWinner(),Color.YELLOW);
	}
	@Test
	public void testgetFieldColors() {
		Ring a = new Ring(Color.GREEN, Tier.MEDIUM);
		field.setRing(new Ring(Color.GREEN, Tier.MEDIUM));
		assertEquals(field.getFieldColors(), 
				new ArrayList<>(Arrays.asList(field.getFieldState().get(0).getColor(),
						field.getFieldState().get(1).getColor(),
						field.getFieldState().get(2).getColor(),
						field.getFieldState().get(3).getColor())));
	}
	@Test
	public void testtoString() throws RinggzException {
		Board b = new Board();
		assertEquals(field.toString(), new String("--0-"));
		assertEquals(b.getField(20).toString(), new String("-20-"));	
		}
}
