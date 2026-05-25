// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract StorageStructBox {
    event PositionSet(address indexed owner, uint256 x, uint256 y, uint256 flags);

    struct Position {
        uint256 x;
        uint256 y;
        uint256 flags;
    }

    mapping(address => Position) private positions;
    Position private last;

    function setFor(
        address owner,
        uint256 x,
        uint256 y
    ) public returns (uint256) {
        Position storage position = positions[owner];
        position.x = x;
        position.y = y;
        position.flags = x + y;
        last = Position({
            x: position.x,
            y: position.y,
            flags: position.flags
        });
        emit PositionSet(owner, position.x, position.y, position.flags);
        return position.flags;
    }

    function moveFor(
        address owner,
        int256 dx,
        int256 dy
    ) public returns (uint256, uint256, uint256) {
        Position storage position = positions[owner];
        if (dx >= 0) {
            position.x += uint256(dx);
        } else {
            position.x -= uint256(-dx);
        }
        if (dy >= 0) {
            position.y += uint256(dy);
        } else {
            position.y -= uint256(-dy);
        }
        position.flags = position.x ^ position.y;
        last = Position({
            x: position.x,
            y: position.y,
            flags: position.flags
        });
        emit PositionSet(owner, position.x, position.y, position.flags);
        return (position.x, position.y, position.flags);
    }

    function readFor(address owner)
        public
        view
        returns (uint256, uint256, uint256)
    {
        Position storage position = positions[owner];
        return (position.x, position.y, position.flags);
    }

    function lastSnapshot() public view returns (uint256, uint256, uint256) {
        return (last.x, last.y, last.flags);
    }

    function clearFor(address owner) public returns (uint256, uint256, uint256) {
        delete positions[owner];
        last = Position({x: 0, y: 0, flags: 0});
        emit PositionSet(owner, 0, 0, 0);
        Position storage position = positions[owner];
        return (position.x, position.y, position.flags);
    }
}
