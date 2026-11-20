// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {ERC20} from "solmate/tokens/ERC20.sol";
import {SolmateVault} from "./SolmateVault.sol";

/// SolmateVault with a harmless function whose loop runs up to 3 times, more
/// than Halmos unrolls by default (2): its keeps check is cut short.
contract LoopVault is SolmateVault {
    event Ping(uint256 k);

    constructor(ERC20 asset_) SolmateVault(asset_) {}

    function ping(uint256 n) external {
        n = n % 4;
        for (uint256 k; k < n; k++) {
            emit Ping(k);
        }
    }
}
