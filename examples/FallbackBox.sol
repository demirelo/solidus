// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract FallbackBox {
    event Hit(uint8 indexed kind, uint256 value, uint256 size);

    uint256 public mode;
    uint256 public last;

    receive() external payable {
        mode = 1;
        last = msg.value;
        emit Hit(1, msg.value, 0);
    }

    fallback(bytes calldata input) external payable returns (bytes memory) {
        mode = 2;
        last = msg.value + input.length;
        emit Hit(2, msg.value, input.length);
        return abi.encode(input.length, msg.value, last);
    }

    function snapshot() public view returns (uint256, uint256) {
        return (mode, last);
    }
}
