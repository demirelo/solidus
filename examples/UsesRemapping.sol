// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import "sample-lib/ScaleLib.sol";

contract UsesRemapping {
    function triple(uint256 value) public pure returns (uint256) {
        return ScaleLib.triple(value);
    }
}
