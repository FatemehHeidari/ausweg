// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC20, ERC20} from "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import {ERC4626} from "@openzeppelin/contracts/token/ERC20/extensions/ERC4626.sol";

/// OpenZeppelin's ERC4626 as a concrete vault. The smoke test uses it for a
/// solver timeout: with no amount bound, the 512-bit branch of its mulDiv
/// keeps queries beyond a five-second limit.
contract OZVault is ERC4626 {
    constructor(IERC20 asset_) ERC20("OZ Vault", "ozvTKN") ERC4626(asset_) {}
}
