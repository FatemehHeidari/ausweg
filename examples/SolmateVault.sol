// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {ERC20} from "solmate/tokens/ERC20.sol";
import {ERC4626} from "solmate/tokens/ERC4626.sol";

/// The smallest concrete vault on Solmate's ERC4626: its assets are the
/// tokens it holds.
contract SolmateVault is ERC4626 {
    constructor(ERC20 asset_) ERC4626(asset_, "Solmate Vault", "svTKN") {}

    function totalAssets() public view override returns (uint256) {
        return asset.balanceOf(address(this));
    }
}
