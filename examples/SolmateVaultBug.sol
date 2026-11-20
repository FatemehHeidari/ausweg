// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {ERC20} from "solmate/tokens/ERC20.sol";
import {FixedPointMathLib} from "solmate/utils/FixedPointMathLib.sol";
import {SolmateVault} from "./SolmateVault.sol";

/// SolmateVault with one planted bug: convertToAssets rounds up, where
/// Solmate rounds down.
contract SolmateVaultBug is SolmateVault {
    using FixedPointMathLib for uint256;

    constructor(ERC20 asset_) SolmateVault(asset_) {}

    function convertToAssets(uint256 shares) public view override returns (uint256) {
        uint256 supply = totalSupply;
        return supply == 0 ? shares : shares.mulDivUp(totalAssets(), supply);
    }
}
