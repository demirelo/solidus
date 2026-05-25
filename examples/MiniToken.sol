// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract MiniToken {
    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    uint256 private supply;
    mapping(address => uint256) private balances;
    mapping(address => mapping(address => uint256)) private allowances;

    constructor(uint256 initialSupply) {
        supply = initialSupply;
        balances[msg.sender] = initialSupply;
        emit Transfer(address(0), msg.sender, initialSupply);
    }

    function totalSupply() public view returns (uint256) {
        return supply;
    }

    function balanceOf(address owner) public view returns (uint256) {
        return balances[owner];
    }

    function myBalance() public view returns (uint256) {
        return balances[msg.sender];
    }

    function myAllowance() public view returns (uint256) {
        return allowances[msg.sender][msg.sender];
    }

    function transfer(address to, uint256 amount) public returns (bool) {
        _transfer(msg.sender, to, amount);
        return true;
    }

    function approveSelf(uint256 amount) public returns (bool) {
        allowances[msg.sender][msg.sender] = amount;
        emit Approval(msg.sender, msg.sender, amount);
        return true;
    }

    function spendSelf(address to, uint256 amount) public returns (bool) {
        uint256 allowed = allowances[msg.sender][msg.sender];
        require(allowed >= amount, "allowance");
        allowances[msg.sender][msg.sender] = allowed - amount;
        _transfer(msg.sender, to, amount);
        return true;
    }

    function _transfer(address from, address to, uint256 amount) private {
        require(to != address(0), "zero");
        uint256 fromBalance = balances[from];
        require(fromBalance >= amount, "balance");
        balances[from] = fromBalance - amount;
        balances[to] += amount;
        emit Transfer(from, to, amount);
    }
}
