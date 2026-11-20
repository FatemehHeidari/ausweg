// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {ERC20} from "solmate/tokens/ERC20.sol";
import {SolmateVault} from "./SolmateVault.sol";

/// SolmateVault with a valid partial-redemption limit: at most 100 shares per
/// call. maxRedeem and maxWithdraw say so, and redeem and withdraw enforce it.
/// A user with more than 100 shares gets out in several calls, never in one.
contract CapRedeemVault is SolmateVault {
    uint256 public constant PER_CALL = 100;

    constructor(ERC20 asset_) SolmateVault(asset_) {}

    function maxRedeem(address owner) public view override returns (uint256) {
        uint256 b = balanceOf[owner];
        return b < PER_CALL ? b : PER_CALL;
    }

    function maxWithdraw(address owner) public view override returns (uint256) {
        return convertToAssets(maxRedeem(owner));
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
