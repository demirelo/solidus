// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract ExternalCallBox {
    error ExternalFailed(bytes data);

    function rawCall(
        address payable target,
        bytes calldata payload,
        uint256 amount
    ) public payable returns (bool, bytes memory) {
        return target.call{value: amount}(payload);
    }

    function rawStaticCall(
        address target,
        bytes calldata payload
    ) public view returns (bool, bytes memory) {
        return target.staticcall(payload);
    }

    function rawDelegateCall(
        address target,
        bytes calldata payload
    ) public returns (bool, bytes memory) {
        return target.delegatecall(payload);
    }

    function bubbleCall(
        address payable target,
        bytes calldata payload
    ) public payable returns (bytes memory) {
        (bool ok, bytes memory data) = target.call{value: msg.value}(payload);
        if (!ok) {
            revert ExternalFailed(data);
        }
        return data;
    }

    function assemblyReturnDataCopy(
        address target
    ) public view returns (uint256 size, bytes32 firstWord) {
        assembly {
            let ptr := mload(0x40)
            let ok := staticcall(gas(), target, 0, 0, ptr, 0x20)
            size := returndatasize()
            returndatacopy(ptr, 0, size)
            firstWord := mload(ptr)
            if iszero(ok) {
                revert(ptr, size)
            }
        }
    }
}
