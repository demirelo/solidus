// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract PayableVault {
    uint256 public total;

    constructor() payable {
        total += msg.value;
    }

    function deposit() public payable returns (uint256) {
        total += msg.value;
        return total;
    }
}
