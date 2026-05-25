// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract InlineAssemblyBox {
    event Stored(uint256 indexed oldValue, uint256 newValue);

    uint256 private value;

    function arithmetic(uint256 left, uint256 right)
        public
        pure
        returns (uint256 sum, uint256 product, uint256 mixed)
    {
        assembly ("memory-safe") {
            sum := add(left, right)
            product := mul(left, right)
            mixed := xor(shl(4, left), shr(1, right))
        }
    }

    function store(uint256 next) public returns (uint256 oldValue) {
        assembly {
            oldValue := sload(value.slot)
            sstore(value.slot, next)
        }
        emit Stored(oldValue, next);
    }

    function load() public view returns (uint256 current) {
        assembly {
            current := sload(value.slot)
        }
    }

    function hash(bytes memory input)
        public
        pure
        returns (bytes32 digest, uint256 length)
    {
        assembly ("memory-safe") {
            length := mload(input)
            digest := keccak256(add(input, 0x20), length)
        }
    }

    function calldataWord(bytes calldata input)
        public
        pure
        returns (bytes32 word, uint256 length)
    {
        assembly {
            word := calldataload(input.offset)
            length := input.length
        }
    }

    function checkedDiv(uint256 denominator) public pure returns (uint256 result) {
        assembly ("memory-safe") {
            if iszero(denominator) {
                mstore(0x00, shl(224, 0x4e487b71))
                mstore(0x04, 0x12)
                revert(0x00, 0x24)
            }
        }
        result = 100 / denominator;
    }
}
