// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

interface IFace {
    function f(uint256 x) external returns (uint256);
}

abstract contract Base {
    function g() public virtual returns (uint256);
}

contract Impl is Base {
    function f(uint256 x) public pure returns (uint256) {
        return x + 1;
    }

    function g() public pure override returns (uint256) {
        return 7;
    }
}
