// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract EnumBytesBox {
    enum Mode {
        Off,
        Warm,
        Hot
    }

    event Changed(Mode indexed mode, bytes4 tag);

    Mode private mode;
    bytes4 private tag;

    constructor(bytes4 initialTag) {
        mode = Mode.Warm;
        tag = initialTag;
    }

    function set(Mode next, bytes4 nextTag) public returns (uint256 score) {
        mode = next;
        tag = nextTag;
        emit Changed(next, nextTag);
        return tagScore(nextTag) + uint8(next);
    }

    function read() public view returns (Mode current, bytes4 currentTag, bool hot) {
        return (mode, tag, mode == Mode.Hot);
    }

    function mix(bytes4 left, bytes4 right)
        public
        pure
        returns (bytes4 mixed, bytes32 widened)
    {
        mixed = left ^ right;
        widened = bytes32(mixed);
    }

    function tagScore(bytes4 input) public pure returns (uint256) {
        return uint8(input[0]) + uint8(input[3]);
    }
}
