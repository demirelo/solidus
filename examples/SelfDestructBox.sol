// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract SelfDestructBox {
    error NotArmed();

    bool public armed;

    constructor() payable {}

    receive() external payable {
        armed = true;
    }

    function arm() public payable returns (uint256) {
        armed = true;
        return address(this).balance;
    }

    function retire(address payable recipient) public {
        if (!armed) revert NotArmed();
        selfdestruct(recipient);
    }

    function retireZero() public {
        assembly ("memory-safe") {
            selfdestruct(0)
        }
    }
}
