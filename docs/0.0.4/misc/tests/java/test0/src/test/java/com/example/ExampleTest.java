// example/src/test/java/com/example/ExampleTest.java

package com.example;

import org.junit.Test;
import org.junit.Assert;

public class ExampleTest {
    @Test
    public void example() {
        int num0 = 10; //
        int num1 = 10; //
        int numX = 20;

        Assert.assertEquals(num0 + num1, numX);
    }
}