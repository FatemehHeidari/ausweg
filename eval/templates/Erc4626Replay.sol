// SPDX-License-Identifier: MIT
pragma solidity >=0.8.0;

// Written by the ausweg evaluation runner. It looks for an exit failure from
// deployment by running the vault under forge's invariant fuzzer, apart from
// ausweg's proof. A failure it finds is a concrete call sequence, which the
// runner then replays as a plain test. The three exit properties are those of
// ausweg's exit checks.
import {Test} from "forge-std/Test.sol";
import "{{IMPORT}}";
import {AuswegEvalToken} from "./ReplayToken.sol";

interface IAuswegEvalVault {
    function balanceOf(address) external view returns (uint256);
    function deposit(uint256, address) external returns (uint256);
    function mint(uint256, address) external returns (uint256);
    function withdraw(uint256, address, address) external returns (uint256);
    function redeem(uint256, address, address) external returns (uint256);
    function transfer(address, uint256) external returns (bool);
    function maxRedeem(address) external view returns (uint256);
    function maxWithdraw(address) external view returns (uint256);
    function previewRedeem(uint256) external view returns (uint256);
    function previewWithdraw(uint256) external view returns (uint256);
}

/// The calls the fuzzer makes: alice, bob and carol deposit, mint, withdraw,
/// redeem and transfer shares; new assets reach a user or the vault itself.
/// A call the vault rejects is skipped.
contract AuswegEvalHandler is Test {
    IAuswegEvalVault public vault;
    AuswegEvalToken public token;
    address[3] public users;

    constructor(IAuswegEvalVault v, AuswegEvalToken t, address[3] memory u) {
        vault = v;
        token = t;
        users = u;
    }

    function _user(uint256 i) internal view returns (address) {
        return users[i % 3];
    }

    function _room() internal view returns (uint256) {
        return 2 ** 96 - token.totalSupply();
    }

    function fund(uint256 i, uint256 amount) external {
        token.mint(_user(i), bound(amount, 0, _room()));
    }

    function donate(uint256 amount) external {
        token.mint(address(vault), bound(amount, 0, _room()));
    }

    function deposit(uint256 i, uint256 assets) external {
        address u = _user(i);
        assets = bound(assets, 0, token.balanceOf(u));
        vm.prank(u);
        try vault.deposit(assets, u) {} catch {}
    }

    function mint(uint256 i, uint256 shares) external {
        address u = _user(i);
        shares = bound(shares, 0, 2 ** 96);
        vm.prank(u);
        try vault.mint(shares, u) {} catch {}
    }

    function withdraw(uint256 i, uint256 assets) external {
        address u = _user(i);
        try vault.maxWithdraw(u) returns (uint256 m) {
            assets = bound(assets, 0, m);
        } catch {
            return;
        }
        vm.prank(u);
        try vault.withdraw(assets, u, u) {} catch {}
    }

    function redeem(uint256 i, uint256 shares) external {
        address u = _user(i);
        shares = bound(shares, 0, vault.balanceOf(u));
        vm.prank(u);
        try vault.redeem(shares, u, u) {} catch {}
    }

    function transfer(uint256 i, uint256 j, uint256 shares) external {
        address u = _user(i);
        shares = bound(shares, 0, vault.balanceOf(u));
        vm.prank(u);
        try vault.transfer(_user(j), shares) {} catch {}
    }
}

/// The deployment and the three exit properties, shared by the search and
/// by every replay.
abstract contract AuswegEvalExits is Test {
    IAuswegEvalVault internal vault;
    AuswegEvalToken internal token;
    AuswegEvalHandler internal handler;
    address[3] internal users = [address(0xA11CE), address(0xB0B), address(0xCA401)];

    function setUp() public virtual {
        token = new AuswegEvalToken();
        vault = IAuswegEvalVault(address(new {{TARGET}}({{CTOR_ARGS}})));
        for (uint256 k = 0; k < 3; k++) {
            vm.prank(users[k]);
            token.approve(address(vault), type(uint256).max);
        }
        handler = new AuswegEvalHandler(vault, token, users);
    }

    /// Full redemption: each user who holds shares redeems all of them in one
    /// call, with no revert, a payout of at least previewRedeem, the asset
    /// transfer equal to it, and no shares left.
    function exitRedeem() public {
        for (uint256 k = 0; k < 3; k++) {
            address u = users[k];
            uint256 s = vault.balanceOf(u);
            if (s == 0) continue;
            uint256 snap = vm.snapshotState();
            uint256 quoted = vault.previewRedeem(s);
            uint256 before = token.balanceOf(u);
            vm.prank(u);
            try vault.redeem(s, u, u) returns (uint256 paid) {
                require(paid >= quoted, "exit redeem: paid less than previewRedeem");
                require(token.balanceOf(u) - before == paid, "exit redeem: the transfer differs from the payout");
                require(vault.balanceOf(u) == 0, "exit redeem: shares left");
            } catch {
                revert("exit redeem: the call reverted");
            }
            vm.revertToState(snap);
        }
    }

    /// Redemption at the advertised limit: a positive maxRedeem quote redeems,
    /// pays at least previewRedeem, and burns exactly the quoted shares.
    function exitMaxRedeem() public {
        for (uint256 k = 0; k < 3; k++) {
            address u = users[k];
            uint256 m = vault.maxRedeem(u);
            if (m == 0) continue;
            uint256 snap = vm.snapshotState();
            uint256 quoted = vault.previewRedeem(m);
            uint256 held = vault.balanceOf(u);
            vm.prank(u);
            try vault.redeem(m, u, u) returns (uint256 paid) {
                require(paid >= quoted, "exit max_redeem: paid less than previewRedeem");
                require(held - vault.balanceOf(u) == m, "exit max_redeem: burned other than the quote");
            } catch {
                revert("exit max_redeem: the call reverted");
            }
            vm.revertToState(snap);
        }
    }

    /// Withdrawal at the advertised limit: a positive maxWithdraw quote
    /// withdraws, burns at most previewWithdraw, and transfers exactly that.
    function exitWithdraw() public {
        for (uint256 k = 0; k < 3; k++) {
            address u = users[k];
            uint256 w = vault.maxWithdraw(u);
            if (w == 0) continue;
            uint256 snap = vm.snapshotState();
            uint256 quoted = vault.previewWithdraw(w);
            uint256 before = token.balanceOf(u);
            vm.prank(u);
            try vault.withdraw(w, u, u) returns (uint256 burned) {
                require(burned <= quoted, "exit withdraw: burned more than previewWithdraw");
                require(token.balanceOf(u) - before == w, "exit withdraw: the transfer differs from the quote");
            } catch {
                revert("exit withdraw: the call reverted");
            }
            vm.revertToState(snap);
        }
    }
}

contract AuswegEvalSearch is AuswegEvalExits {
    function setUp() public override {
        super.setUp();
        targetContract(address(handler));
    }

    function invariant_exit_redeem() public {
        exitRedeem();
    }

    function invariant_exit_max_redeem() public {
        exitMaxRedeem();
    }

    function invariant_exit_withdraw() public {
        exitWithdraw();
    }
}
