// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract StorageArrayBox {
    event ArrayChanged(uint256 indexed length, uint256 value);

    uint256[] private values;

    function length() public view returns (uint256) {
        return values.length;
    }

    function at(uint256 index) public view returns (uint256) {
        return values[index];
    }

    function pushOne(uint256 value) public returns (uint256) {
        values.push(value);
        emit ArrayChanged(values.length, value);
        return values.length;
    }

    function pushMany(uint256[] calldata items) public returns (uint256) {
        for (uint256 i = 0; i < items.length; i++) {
            values.push(items[i]);
            emit ArrayChanged(values.length, items[i]);
        }
        return values.length;
    }

    function setAt(uint256 index, uint256 value) public returns (uint256) {
        values[index] = value;
        emit ArrayChanged(values.length, value);
        return values[index];
    }

    function popOne() public returns (uint256) {
        require(values.length != 0, "empty");
        uint256 value = values[values.length - 1];
        values.pop();
        emit ArrayChanged(values.length, value);
        return value;
    }

    function sum() public view returns (uint256 total) {
        for (uint256 i = 0; i < values.length; i++) {
            total += values[i];
        }
    }
}
