// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract ModifierBase {
    uint256 internal base;

    constructor(uint256 initial) {
        base = initial;
    }

    modifier capped(uint256 value) {
        require(value <= 100, "too big");
        _;
    }

    function scale(uint256 value) public pure virtual returns (uint256) {
        return value + 1;
    }
}

contract ModifierBox is ModifierBase {
    error TooSmall(uint256 value);

    uint256 public hits;

    constructor(uint256 initial) ModifierBase(initial) {}

    modifier bump() {
        hits += 1;
        _;
        hits += 2;
    }

    function scale(uint256 value) public pure override returns (uint256) {
        return value * 2 + 1;
    }

    function guarded(uint256 value)
        public
        capped(value)
        bump
        returns (uint256)
    {
        if (value < base) revert TooSmall(value);
        base += value;
        return scale(base);
    }

    function read() public view returns (uint256 current, uint256 count) {
        return (base, hits);
    }
}
