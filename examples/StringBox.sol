// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract StringBox {
    function greet() public pure returns (string memory) {
        return "hello";
    }

    function echo(string calldata value) public pure returns (string memory) {
        return value;
    }

    function len(string calldata value) public pure returns (uint256) {
        return bytes(value).length;
    }
}
