// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract ChildBox {
    uint256 public value;

    constructor(uint256 seed) payable {
        value = seed + msg.value;
    }

    function read() public view returns (uint256) {
        return value + 7;
    }
}

contract FactoryBox {
    event Made(uint256 value);

    uint256 public last;

    function make(uint256 seed) public payable returns (uint256) {
        ChildBox child = new ChildBox{value: msg.value}(seed);
        uint256 result = child.read();
        last = result;
        emit Made(result);
        return result;
    }

    function makeTwice(uint256 left, uint256 right)
        public
        returns (uint256, uint256)
    {
        ChildBox first = new ChildBox(left);
        ChildBox second = new ChildBox(right);
        return (first.read(), second.read());
    }

    function makeSalted(bytes32 salt, uint256 seed)
        public
        payable
        returns (address, uint256)
    {
        ChildBox child = new ChildBox{salt: salt, value: msg.value}(seed);
        uint256 result = child.read();
        last = result;
        emit Made(result);
        return (address(child), result);
    }
}
