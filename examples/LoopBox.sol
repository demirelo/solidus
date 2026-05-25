// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract LoopBox {
    function sum(uint256[] calldata values) public pure returns (uint256 total) {
        for (uint256 i = 0; i < values.length; i++) {
            total += values[i];
        }
    }

    function countTo(uint256 n) public pure returns (uint256 total) {
        for (uint256 i = 0; i < n; i++) {
            total += i;
        }
    }

    function skipOddBefore(uint256 n) public pure returns (uint256 total) {
        for (uint256 i = 0; i < n; i++) {
            if (i == 6) {
                break;
            }
            if (i % 2 == 1) {
                continue;
            }
            total += i;
        }
    }
}
