// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

contract ConstructorCounter {
    uint256 public value;

    constructor(uint256 initial) {
        value = initial;
    }

    function add(uint256 amount) public {
        value = value + amount;
    }
}
