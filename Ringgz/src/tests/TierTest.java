package tests;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;
import model.*;

public class TierTest {
    private Tier SMALLEST;
    private Tier SMALL;
    private Tier MEDIUM;
    private Tier LARGE;
    private Tier base;
    private Tier init;

    @Before
    public void setUp() throws Exception {
        SMALLEST = Tier.SMALLEST;
        SMALL = Tier.SMALL;
        MEDIUM = Tier.MEDIUM;
        LARGE = Tier.LARGE;
        base = Tier.BASE;
        init = Tier.INIT;
    }

    @Test
    public void testToChar() {
        assertTrue(Tier.toTier(1) == Tier.BASE);
        assertTrue(Tier.toTier(2) == Tier.SMALLEST);
        assertTrue(Tier.toTier(3) == Tier.SMALL);
        assertTrue(Tier.toTier(4) == Tier.MEDIUM);
        assertTrue(Tier.toTier(5) == Tier.LARGE);
        assertTrue(Tier.toTier(10) == null);
        assertFalse(Tier.toTier(1) == Tier.INIT);
        assertFalse(Tier.toTier(2) == Tier.INIT);
        assertFalse(Tier.toTier(3) == Tier.INIT);
        assertFalse(Tier.toTier(4) == Tier.INIT);
        assertFalse(Tier.toTier(5) == Tier.INIT);
    }

    @Test
    public void testOccupied() {
        assertTrue(SMALLEST.occupied());
        assertTrue(SMALL.occupied());
        assertTrue(MEDIUM.occupied());
        assertTrue(LARGE.occupied());
        assertTrue(base.occupied());
        assertFalse(init.occupied());

    }
}
