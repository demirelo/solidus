// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract MappingCounter {
    mapping(uint256 => uint256) public counts;

    function inc(uint256 key) public returns (uint256) {
        counts[key] += 1;
        return counts[key];
    }

    function add(uint256 key, uint256 amount) public returns (uint256) {
        counts[key] += amount;
        return counts[key];
    }
}
