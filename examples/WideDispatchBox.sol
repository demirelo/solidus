// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @notice A wide external surface: 40 distinct selectors with deliberately tiny
/// bodies. The point is to stress the compiler's PUBLIC-FUNCTION DISPATCHER (the
/// selector comparison/sort tree that solc's via-IR backend emits at the top of
/// the runtime object) without inflating per-function code. Signatures are
/// varied (uint256/int256/address/bytes32/bool/tuple args, pure/view/nonpayable)
/// so the dispatch table is not a trivial run of identical shapes.
contract WideDispatchBox {
    mapping(uint256 => uint256) private slot;
    uint256 private cursor;

    // --- pure scalar ops (distinct arithmetic per selector) ---
    function addU(uint256 a, uint256 b) external pure returns (uint256) { return a + b; }
    function subU(uint256 a, uint256 b) external pure returns (uint256) { return a - b; }
    function mulU(uint256 a, uint256 b) external pure returns (uint256) { return a * b; }
    function divU(uint256 a, uint256 b) external pure returns (uint256) { return a / b; }
    function modU(uint256 a, uint256 b) external pure returns (uint256) { return a % b; }
    function expU(uint256 a, uint256 b) external pure returns (uint256) { return a ** b; }
    function minU(uint256 a, uint256 b) external pure returns (uint256) { return a < b ? a : b; }
    function maxU(uint256 a, uint256 b) external pure returns (uint256) { return a > b ? a : b; }
    function avgU(uint256 a, uint256 b) external pure returns (uint256) { return (a & b) + ((a ^ b) >> 1); }
    function gcdStep(uint256 a, uint256 b) external pure returns (uint256) { return b == 0 ? a : a % b; }

    // --- pure bitwise / shift ops ---
    function andB(uint256 a, uint256 b) external pure returns (uint256) { return a & b; }
    function orB(uint256 a, uint256 b) external pure returns (uint256) { return a | b; }
    function xorB(uint256 a, uint256 b) external pure returns (uint256) { return a ^ b; }
    function notB(uint256 a) external pure returns (uint256) { return ~a; }
    function shl(uint256 a, uint256 n) external pure returns (uint256) { return a << n; }
    function shr(uint256 a, uint256 n) external pure returns (uint256) { return a >> n; }
    function sar(int256 a, uint256 n) external pure returns (int256) { return a >> n; }
    function byteAt(uint256 i, uint256 w) external pure returns (uint256 r) { assembly { r := byte(i, w) } }
    function clzWord(uint256 a) external pure returns (uint256 r) { r = a == 0 ? 256 : 0; }
    function popLow(uint256 a) external pure returns (uint256) { return a & 1; }

    // --- signed ops ---
    function addS(int256 a, int256 b) external pure returns (int256) { return a + b; }
    function subS(int256 a, int256 b) external pure returns (int256) { return a - b; }
    function mulS(int256 a, int256 b) external pure returns (int256) { return a * b; }
    function negS(int256 a) external pure returns (int256) { return -a; }
    function absS(int256 a) external pure returns (uint256) { return a < 0 ? uint256(-a) : uint256(a); }

    // --- hashing / encoding ---
    function hashOne(bytes32 x) external pure returns (bytes32) { return keccak256(abi.encode(x)); }
    function hashTwo(bytes32 x, bytes32 y) external pure returns (bytes32) { return keccak256(abi.encodePacked(x, y)); }
    function selectorOf(bytes4 s) external pure returns (uint256) { return uint256(uint32(s)); }
    function packAddr(address a, uint96 tag) external pure returns (bytes32) { return bytes32((uint256(uint160(a)) << 96) | tag); }
    function unpackTag(bytes32 p) external pure returns (uint96) { return uint96(uint256(p)); }

    // --- boolean / comparison ---
    function eqU(uint256 a, uint256 b) external pure returns (bool) { return a == b; }
    function ltU(uint256 a, uint256 b) external pure returns (bool) { return a < b; }
    function bothNonzero(uint256 a, uint256 b) external pure returns (bool) { return a != 0 && b != 0; }
    function inRange(uint256 x, uint256 lo, uint256 hi) external pure returns (bool) { return x >= lo && x <= hi; }
    function pickPair(bool c, uint256 a, uint256 b) external pure returns (uint256, uint256) { return c ? (a, b) : (b, a); }

    // --- stateful (SSTORE/SLOAD across a few selectors) ---
    function poke(uint256 key, uint256 val) external returns (uint256) { slot[key] = val; return val; }
    function bump(uint256 key) external returns (uint256) { return ++slot[key]; }
    function advance() external returns (uint256) { return ++cursor; }
    function peek(uint256 key) external view returns (uint256) { return slot[key]; }
    function where() external view returns (uint256) { return cursor; }
}
