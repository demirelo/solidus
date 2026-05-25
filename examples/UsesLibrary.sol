// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import "./MathLib.sol";

contract UsesLibrary {
    function twice(uint256 value) public pure returns (uint256) {
        return MathLib.twice(value);
    }
}
