// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract ConstructorAbiBox {
    bytes32 public immutable digest;
    uint256 public immutable totalLength;

    constructor(bytes memory payload, string memory label) {
        digest = keccak256(abi.encode(payload, label));
        totalLength = payload.length + bytes(label).length;
    }

    function check(bytes calldata payload, string calldata label)
        public
        view
        returns (bool matchesDigest, uint256 storedLength)
    {
        return (digest == keccak256(abi.encode(payload, label)), totalLength);
    }

    function lengths() public view returns (uint256) {
        return totalLength;
    }
}
