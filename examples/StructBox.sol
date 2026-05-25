// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract StructBox {
    struct Pair {
        uint256 a;
        uint256 b;
    }

    function pack(uint256 a, uint256 b)
        public
        pure
        returns (uint256 first, uint256 second, uint256 total)
    {
        Pair memory pair = Pair({a: a, b: b});
        return (pair.a, pair.b, pair.a + pair.b);
    }

    function swapAndSum(uint256 a, uint256 b) public pure returns (uint256) {
        Pair memory original = Pair({a: a, b: b});
        Pair memory swapped = Pair({a: original.b, b: original.a});
        return swapped.a + swapped.b;
    }

    function fromArray(uint256[] calldata values) public pure returns (uint256) {
        Pair memory pair;
        if (values.length > 0) {
            pair.a = values[0];
        }
        if (values.length > 1) {
            pair.b = values[1];
        }
        return pair.a + pair.b;
    }
}
