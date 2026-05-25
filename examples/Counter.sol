// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

contract Counter {
    uint256 public value;

    function inc() public {
        value = value + 1;
    }

    function add(uint256 amount) public {
        value = value + amount;
    }
}
