// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract ArrayBox {
    function len(uint256[] calldata xs) public pure returns (uint256) {
        return xs.length;
    }

    function firstOrZero(uint256[] calldata xs) public pure returns (uint256) {
        if (xs.length == 0) {
            return 0;
        }
        return xs[0];
    }
}
