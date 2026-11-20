// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {ERC20} from "solmate/tokens/ERC20.sol";
import {SolmateVault} from "./SolmateVault.sol";

/// SolmateVault that lets a user take out at most half their shares at a time,
/// rounded down: a user left with 1 share can never get it out.
contract HalfExitVault is SolmateVault {
    constructor(ERC20 asset_) SolmateVault(asset_) {}

    function maxRedeem(address owner) public view override returns (uint256) {
        return balanceOf[owner] / 2;
    }

    function maxWithdraw(address owner) public view override returns (uint256) {
        return convertToAssets(balanceOf[owner] / 2);
    }

    function redeem(uint256 shares, address receiver, address owner) public override returns (uint256) {
        require(shares <= maxRedeem(owner), "MAX_REDEEM");
        return super.redeem(shares, receiver, owner);
    }

    function withdraw(uint256 assets, address receiver, address owner) public override returns (uint256) {
        require(assets <= maxWithdraw(owner), "MAX_WITHDRAW");
        return super.withdraw(assets, receiver, owner);
    }
}
