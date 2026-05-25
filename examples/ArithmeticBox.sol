// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract ArithmeticBox {
    function checkedAdd(uint256 left, uint256 right)
        public
        pure
        returns (uint256)
    {
        return left + right;
    }

    function uncheckedAdd(uint256 left, uint256 right)
        public
        pure
        returns (uint256 result)
    {
        unchecked {
            result = left + right;
        }
    }

    function checkedSub(uint256 left, uint256 right)
        public
        pure
        returns (uint256)
    {
        return left - right;
    }

    function uncheckedSub(uint256 left, uint256 right)
        public
        pure
        returns (uint256 result)
    {
        unchecked {
            result = left - right;
        }
    }

    function checkedMul(uint256 left, uint256 right)
        public
        pure
        returns (uint256)
    {
        return left * right;
    }

    function divided(uint256 left, uint256 right)
        public
        pure
        returns (uint256)
    {
        return left / right;
    }
}
