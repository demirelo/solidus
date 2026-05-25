// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract BitwiseBox {
    function bitwise(uint256 a, uint256 b)
        public
        pure
        returns (uint256 anded, uint256 ored, uint256 xored)
    {
        return (a & b, a | b, a ^ b);
    }

    function shifts(uint256 value, uint256 amount)
        public
        pure
        returns (uint256 left, uint256 right)
    {
        return (value << amount, value >> amount);
    }

    function signedMath(int256 a, int256 b)
        public
        pure
        returns (int256 quotient, int256 remainder, int256 shifted)
    {
        return (a / b, a % b, a >> 3);
    }
}
