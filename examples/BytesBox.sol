// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract BytesBox {
    function echo(bytes calldata data) public pure returns (bytes memory) {
        return data;
    }
}
