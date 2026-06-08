// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

contract ResourceObserverBox {
    function observe() external view returns (uint256 value) {
        assembly ("memory-safe") {
            pop(gas())
            pop(msize())
            mstore(0, 0x2a)
            return(0, 32)
        }
    }
}
