// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

error OutOfRange(uint256 seen, uint256 max);

contract ErrorPanicBox {
    event Checked(uint256 indexed value, uint256 doubled);

    uint256 public last;

    constructor(uint256 seed) {
        last = seed;
    }

    function checked(uint256 value) external returns (uint256) {
        if (value > 10) {
            revert OutOfRange(value, 10);
        }

        uint256 doubled = value * 2;
        last = doubled;
        emit Checked(value, doubled);
        return doubled + last;
    }

    function mustBeNonzero(uint256 value) external pure returns (uint256) {
        require(value != 0, "zero");
        return 100 / value;
    }

    function assertSmall(uint256 value) external pure returns (uint256) {
        assert(value < 5);
        return value + 1;
    }

    function uncheckedWrap(uint256 value) external pure returns (uint256) {
        unchecked {
            return value + type(uint256).max;
        }
    }
}
