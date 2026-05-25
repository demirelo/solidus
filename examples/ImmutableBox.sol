// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

contract ImmutableBox {
    uint256 public immutable seed;

    constructor(uint256 value) {
        seed = value;
    }

    function plus(uint256 x) public view returns (uint256) {
        return seed + x;
    }
}
