// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract EventCounter {
    event Bumped(address indexed sender, uint256 oldValue, uint256 newValue);

    uint256 public value;

    function bump(uint256 amount) public {
        uint256 oldValue = value;
        uint256 newValue = oldValue + amount;
        value = newValue;
        emit Bumped(msg.sender, oldValue, newValue);
    }
}
