// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract EnvBox {
    function sender() public view returns (address) {
        return msg.sender;
    }

    function origin() public view returns (address) {
        return tx.origin;
    }

    function chainAndBlock() public view returns (uint256, uint256, uint256) {
        return (block.chainid, block.number, block.timestamp);
    }

    function blockDetails()
        public
        view
        returns (address, uint256, uint256, uint256, uint256)
    {
        return (
            block.coinbase,
            block.gaslimit,
            block.basefee,
            block.prevrandao,
            tx.gasprice
        );
    }

    function echoValue() public payable returns (uint256) {
        return msg.value;
    }

    function balanceAndValue() public payable returns (uint256, uint256) {
        return (address(this).balance, msg.value);
    }
}
