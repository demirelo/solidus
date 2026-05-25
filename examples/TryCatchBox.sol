// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract TryCatchTarget {
    error Custom(uint256 code);

    function maybe(uint256 mode) external returns (uint256) {
        if (mode == 0) {
            return 7;
        }
        if (mode == 1) {
            revert("try-error");
        }
        if (mode == 2) {
            assert(false);
        }
        revert Custom(mode);
    }
}

contract TryCatchBox {
    event Caught(uint256 indexed kind, uint256 value);

    function callMaybe(address target, uint256 mode) public returns (uint256) {
        try TryCatchTarget(target).maybe(mode) returns (uint256 value) {
            emit Caught(0, value);
            return value + 1;
        } catch Error(string memory reason) {
            uint256 length = bytes(reason).length;
            emit Caught(1, length);
            return length;
        } catch Panic(uint256 code) {
            emit Caught(2, code);
            return code;
        } catch (bytes memory data) {
            emit Caught(3, data.length);
            return data.length;
        }
    }
}
