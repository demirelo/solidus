// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract PackedStorageBox {
    enum Mode {
        Cold,
        Warm,
        Hot
    }

    bool public flag;
    uint8 public small;
    int16 public signedSmall;
    uint32 public count;
    Mode public mode;
    address public owner;

    struct Pair {
        uint128 left;
        uint64 right;
        bool enabled;
    }

    Pair public pair;

    function seed() public returns (bool, uint8, int16, uint32, Mode) {
        flag = true;
        small = 7;
        signedSmall = -3;
        count = 99;
        mode = Mode.Warm;
        owner = msg.sender;
        pair = Pair({left: 5, right: 6, enabled: true});
        return (flag, small, signedSmall, count, mode);
    }

    function snapshot()
        public
        view
        returns (
            bool,
            uint8,
            int16,
            uint32,
            Mode,
            address,
            uint128,
            uint64,
            bool
        )
    {
        return (
            flag,
            small,
            signedSmall,
            count,
            mode,
            owner,
            pair.left,
            pair.right,
            pair.enabled
        );
    }

    function mutate(
        uint8 newSmall,
        int16 newSigned,
        uint32 newCount,
        bool newFlag,
        Mode newMode
    ) public returns (bool, uint8, int16, uint32, Mode) {
        small = newSmall;
        signedSmall = newSigned;
        count = newCount;
        flag = newFlag;
        mode = newMode;
        return (flag, small, signedSmall, count, mode);
    }

    function setPair(
        uint128 left,
        uint64 right,
        bool enabled
    ) public returns (uint128, uint64, bool) {
        pair = Pair({left: left, right: right, enabled: enabled});
        return (pair.left, pair.right, pair.enabled);
    }

    function flip() public returns (bool) {
        flag = !flag;
        return flag;
    }
}
