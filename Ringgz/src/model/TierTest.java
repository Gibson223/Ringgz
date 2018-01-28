package model;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

class TierTest {

	@Test
	void toTierTest() {
		assertEquals(Tier.toTier(1), Tier.SMALL);
		assertEquals(Tier.toTier(2), Tier.MEDIUM);
		assertEquals(Tier.toTier(3), Tier.LARGE);
		assertEquals(Tier.toTier(4), Tier.LARGEST);
		assertEquals(Tier.toTier(5), Tier.BASE);
	}

}
