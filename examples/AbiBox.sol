// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract AbiBox {
    function pair(uint256 value, address who)
        public
        pure
        returns (uint256 next, address echoed, bool isZero)
    {
        return (value + 1, who, who == address(0));
    }

    function encodeStatic(uint256 value, address who)
        public
        pure
        returns (bytes memory)
    {
        return abi.encode(value, who);
    }

    function decodeStatic(bytes calldata payload)
        public
        pure
        returns (uint256 value, address who)
    {
        return abi.decode(payload, (uint256, address));
    }

    function encodeDynamic(uint256 value, bytes calldata data)
        public
        pure
        returns (bytes memory)
    {
        return abi.encode(value, data);
    }

    function decodeDynamic(bytes calldata payload)
        public
        pure
        returns (uint256 adjusted, bytes32 dataHash)
    {
        (uint256 value, bytes memory data) = abi.decode(payload, (uint256, bytes));
        return (value + data.length, keccak256(data));
    }
}
