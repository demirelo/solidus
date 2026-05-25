// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract EventMatrix {
    event Plain(uint256 value);
    event One(address indexed sender, uint256 value);
    event Two(address indexed sender, bytes32 indexed salt, uint256 value);
    event Three(
        address indexed sender,
        bytes32 indexed salt,
        uint256 indexed key,
        uint256 value
    );
    event AnonymousZero(uint256 value) anonymous;
    event AnonymousFour(
        address indexed sender,
        bytes32 indexed salt,
        uint256 indexed key,
        uint256 indexed extra
    ) anonymous;

    fallback() external {
        emit AnonymousZero(11);
        emit Plain(22);
        emit One(msg.sender, 33);
        emit Two(msg.sender, bytes32(uint256(44)), 55);
        emit Three(msg.sender, bytes32(uint256(44)), 55, 66);
        emit AnonymousFour(msg.sender, bytes32(uint256(77)), 88, 99);
        assembly ("memory-safe") {
            return(0, 0)
        }
    }
}
