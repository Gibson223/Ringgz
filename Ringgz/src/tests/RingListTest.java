package tests;

import model.Color;
import model.Ring;

import static org.junit.Assert.assertTrue;

import java.util.List;
import java.util.stream.Collectors;

import org.junit.Before;
import org.junit.Test;

import model.RingList;

public class RingListTest {
    public RingList a = new RingList();
    public RingList b;

    @Test
    public void test() {
        assertTrue(a.availableRings.stream().filter(a -> a.getColor() == Color.BLUE).count() == 15);
        assertTrue(
                a.availableRings.stream().filter(a -> a.getColor() == Color.YELLOW).count() == 15);
        assertTrue(a.availableRings.stream().filter(a -> a.getColor() == Color.RED).count() == 15);
        assertTrue(
                a.availableRings.stream().filter(a -> a.getColor() == Color.GREEN).count() == 15);
        assertTrue(a.availableRings.size() == 60);
        List<Ring> listshortened = a.availableRings.stream()
                .filter(a -> a.getColor() == Color.GREEN).collect(Collectors.toList());
        b = new RingList(listshortened);
        assertTrue(b.availableRings.size() == 15);
    }
}
