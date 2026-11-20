// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {ERC20} from "solmate/tokens/ERC20.sol";
import {SolmateVault} from "./SolmateVault.sol";

/// SolmateVault with a function anyone can call to send all of the vault's
/// assets away. It takes an array, which the proof cannot fill in.
contract SweepVault is SolmateVault {
    constructor(ERC20 asset_) SolmateVault(asset_) {}

    function sweep(address[] calldata to) external {
        asset.transfer(to[0], asset.balanceOf(address(this)));
    }
}
