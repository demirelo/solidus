// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract RevertReason {
    error Bad(uint256 value);

    function failIfSeven(uint256 value) public pure returns (uint256) {
        if (value == 7) {
            revert Bad(value);
        }
        return value + 1;
    }

    function reason() public pure {
        revert("nope");
    }
}
