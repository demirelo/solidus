// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @notice A small on-chain accounting/risk engine whose external entry points
/// all funnel through a shared set of non-recursive internal helpers. The point
/// is a DEEP INTERNAL CALL GRAPH: each helper is invoked from several call
/// sites, so the via-IR + Yul backend materializes shared internal functions
/// that are reused (rather than inlined) across the object — the procedure-reuse
/// structure where the remaining size gap vs solc concentrates. No helper is
/// recursive, so the stack-headroom certificate is satisfied.
contract ProcedureReuseBox {
    error OutOfRange(uint256 value, uint256 limit);
    error Insufficient(uint256 have, uint256 want);

    event Settled(address indexed who, uint256 amount, uint256 fee, uint256 net);
    event Rebalanced(uint256 total, uint256 score);

    uint256 private constant BPS = 10_000;

    mapping(address => uint256) private ledger;
    mapping(address => uint256) private weightOf;
    uint256 private totalWeight;
    uint256 private reserve;

    // ---- shared internal helpers (each called from >=2 external sites) ----

    function _clamp(uint256 x, uint256 lo, uint256 hi)
        private
        pure
        returns (uint256)
    {
        if (x < lo) return lo;
        if (x > hi) return hi;
        return x;
    }

    function _requireRange(uint256 x, uint256 limit) private pure {
        if (x > limit) revert OutOfRange(x, limit);
    }

    function _mulDiv(uint256 a, uint256 b, uint256 d)
        private
        pure
        returns (uint256)
    {
        if (d == 0) revert OutOfRange(d, 1);
        unchecked {
            // Bounded operands (callers pre-clamp), so a*b cannot overflow the
            // checked path; keep the checked multiply for realism.
            return (a * b) / d;
        }
    }

    function _bps(uint256 x, uint256 rateBps) private pure returns (uint256) {
        return _mulDiv(x, rateBps, BPS);
    }

    function _blend(uint256 a, uint256 b, uint256 wBps)
        private
        pure
        returns (uint256)
    {
        uint256 wa = _bps(a, wBps);
        uint256 wb = _bps(b, BPS - wBps);
        return wa + wb;
    }

    function _fee(uint256 amount, uint256 rateBps)
        private
        pure
        returns (uint256)
    {
        uint256 raw = _bps(amount, _clamp(rateBps, 1, 500));
        return _clamp(raw, 1, amount);
    }

    function _hashKey(address who, uint256 salt) private pure returns (uint256) {
        return uint256(keccak256(abi.encodePacked(who, salt)));
    }

    function _accrue(uint256 principal, uint256 rateBps, uint256 periods)
        private
        pure
        returns (uint256)
    {
        _requireRange(periods, 64);
        uint256 acc = principal;
        for (uint256 i = 0; i < periods; i++) {
            acc = acc + _bps(acc, rateBps);
        }
        return acc;
    }

    function _score(uint256 a, uint256 b, uint256 c)
        private
        pure
        returns (uint256)
    {
        uint256 mid = _blend(a, b, 6000);
        uint256 lifted = _accrue(mid, 25, 3);
        return _clamp(lifted + _bps(c, 1500), 0, type(uint128).max);
    }

    function _debit(address who, uint256 amount) private returns (uint256) {
        uint256 bal = ledger[who];
        if (bal < amount) revert Insufficient(bal, amount);
        uint256 next = bal - amount;
        ledger[who] = next;
        return next;
    }

    function _credit(address who, uint256 amount) private returns (uint256) {
        uint256 next = ledger[who] + amount;
        ledger[who] = next;
        return next;
    }

    // ---- external entry points (each reuses several helpers) ----

    function deposit(uint256 amount) external returns (uint256 balance) {
        _requireRange(amount, type(uint96).max);
        balance = _credit(msg.sender, amount);
        reserve += _fee(amount, 30);
    }

    function quote(uint256 amount, uint256 rateBps)
        external
        pure
        returns (uint256 fee, uint256 net)
    {
        _requireRange(amount, type(uint96).max);
        fee = _fee(amount, rateBps);
        net = amount - fee;
    }

    function settle(address to, uint256 amount, uint256 rateBps)
        external
        returns (uint256 net)
    {
        _requireRange(amount, type(uint96).max);
        uint256 fee = _fee(amount, rateBps);
        _debit(msg.sender, amount);
        net = amount - fee;
        _credit(to, net);
        reserve += fee;
        emit Settled(msg.sender, amount, fee, net);
    }

    function setWeight(uint256 w) external returns (uint256 total) {
        uint256 clamped = _clamp(w, 1, BPS);
        totalWeight = totalWeight + clamped - weightOf[msg.sender];
        weightOf[msg.sender] = clamped;
        total = totalWeight;
    }

    function rebalance(uint256 seed)
        external
        returns (uint256 total, uint256 score)
    {
        uint256 a = _hashKey(msg.sender, seed) % 1_000_000;
        uint256 b = ledger[msg.sender];
        uint256 c = reserve;
        score = _score(a, b, c);
        total = _accrue(totalWeight, 10, 4);
        emit Rebalanced(total, score);
    }

    function preview(uint256 principal, uint256 rateBps, uint256 periods)
        external
        pure
        returns (uint256 grown, uint256 gain)
    {
        grown = _accrue(_clamp(principal, 1, type(uint96).max), rateBps, periods);
        gain = grown - principal;
    }

    function scoreOf(uint256 a, uint256 b, uint256 c)
        external
        pure
        returns (uint256)
    {
        return _score(a, b, c);
    }

    function balanceOf(address who) external view returns (uint256) {
        return ledger[who];
    }

    function stats() external view returns (uint256, uint256) {
        return (totalWeight, reserve);
    }
}
