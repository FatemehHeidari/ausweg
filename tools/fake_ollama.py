"""Stand-in for Ollama's /api/generate, for testing ausweg's milestone-2 harness with
real forge. Plans are hand-written: six standard ERC-4626 invariants for every
vault, plus one broken assertion on OZVault to exercise the repair loop.
Usage: python3 -I fake_ollama.py <port> <log-file> [standard|strong|model14b|users|only:<id>] [prompt-folder]
"""

import http.server
import json
import re
import sys

PORT = int(sys.argv[1])
LOG = sys.argv[2]
SET = sys.argv[3] if len(sys.argv) > 3 else "standard"
# Optional: a folder to save each prompt in, to check what ausweg sends.
DUMP = sys.argv[4] if len(sys.argv) > 4 else None

ERC4626 = [
    ("solvency", "The vault can always pay out every share it has issued",
     "assertLe(target.convertToAssets(target.totalSupply()), target.totalAssets());"),
    ("supply_matches_balances", "Total supply equals the sum of all users' share balances",
     "assertEq(target.totalSupply(), handler.sumBalanceOf());"),
    ("no_free_round_trip", "Converting assets to shares and back never creates assets",
     "assertLe(target.convertToAssets(target.convertToShares(1e18)), 1e18);"),
    ("deposit_rounds_down", "previewDeposit never promises more shares than the exact conversion",
     "assertLe(target.previewDeposit(1e18), target.convertToShares(1e18));"),
    ("mint_rounds_up", "previewMint never charges fewer assets than the exact conversion",
     "assertGe(target.previewMint(1e18), target.convertToAssets(1e18));"),
    ("withdraw_rounds_up", "previewWithdraw never burns fewer shares than the exact conversion",
     "assertGe(target.previewWithdraw(1e18), target.convertToShares(1e18));"),
    ("redeem_rounds_down", "previewRedeem never pays more assets than the exact conversion",
     "assertLe(target.previewRedeem(1e18), target.convertToAssets(1e18));"),
]

# Round-trip and sum checks that do not hold with equality when a rounding
# direction is flipped. Used to test what the harness can catch at best.
STRONG = [
    ("pays_every_max_withdraw", "The vault holds enough to pay every user's maximum withdrawal at once",
     "assertLe(handler.sumMaxWithdraw(), asset.balanceOf(address(target)));"),
    ("withdraw_charges_enough_shares", "The shares previewWithdraw charges are worth at least the assets",
     "assertGe(target.convertToAssets(target.previewWithdraw(1e18)), 1e18);"),
    ("mint_charges_enough_assets", "The assets previewMint charges are worth at least the shares",
     "assertGe(target.convertToShares(target.previewMint(1e18)), 1e18);"),
    ("convert_matches_redeem", "Without fees, convertToAssets equals previewRedeem",
     "assertEq(target.convertToAssets(1e18), target.previewRedeem(1e18));"),
]

# Shaped like qwen2.5-coder:14b's first answers: four checks that can never
# fail, one real invariant and one wrong one.
MODEL14B = [
    ("max_deposit_greater_zero", "The maximum deposit is never negative",
     "assertGe(target.maxDeposit(address(this)), 0);"),
    ("max_withdraw_greater_zero", "The maximum withdrawals are never negative",
     "assertGe(handler.sumMaxWithdraw(), 0);"),
    ("total_supply_non_negative", "The total supply is never negative",
     "assertTrue(target.totalSupply() >= 0);"),
    ("asset_balance_non_negative", "The vault's asset balance is never negative",
     "assertLe(0, asset.balanceOf(address(target)));"),
    ("total_supply_shares", "Total supply equals the sum of the users' shares",
     "assertEq(target.totalSupply(), handler.sumBalanceOf());"),
    ("total_assets_balance", "Total assets equal all the asset tokens in existence",
     "assertEq(target.totalAssets(), asset.totalSupply());"),
]

# Assertions that name the users: two copied from the 0.2.2 Solmate run, where
# they failed with "Undeclared identifier", and two that show the names point
# at the addresses the handler trades with.
USERS = [
    ("preview_redeem_rounding", "previewRedeem rounds down for alice's shares",
     "assertLe(target.previewRedeem(target.balanceOf(alice)), target.convertToAssets(target.balanceOf(alice)));"),
    ("preview_mint_rounding", "previewMint rounds up for alice's shares",
     "assertGe(target.previewMint(target.balanceOf(alice)), target.convertToAssets(target.balanceOf(alice)));"),
    ("alice_never_holds_shares", "Fails once alice holds shares, so it should be flagged",
     "assertEq(target.balanceOf(alice), 0);"),
    ("users_hold_every_share", "The three named users hold every share",
     "assertEq(target.balanceOf(alice) + target.balanceOf(bob) + target.balanceOf(carol), target.totalSupply());"),
]

# Replacements: round 1 has one that still can never fail; round 2 replaces it.
REPLACE_1 = [STRONG[1], STRONG[0],
             ("still_non_negative", "Total assets are never negative",
              "assertTrue(target.totalAssets() >= 0);")]
REPLACE_2 = [STRONG[2]]

CTOR = {
    "SolmateVault": [{"param": "asset_", "value": "mock_token"}],
    "OZVault": [{"param": "asset_", "value": "mock_token"}],
    "OZFeeVault": [{"param": "asset_", "value": "mock_token"},
                   {"param": "treasury_", "value": "new_address"}],
    "SoladyVault": [{"param": "asset_", "value": "mock_token"}],
}


def plan_for(name):
    chosen = ERC4626 + (STRONG if SET == "strong" else [])
    if SET == "model14b":
        chosen = MODEL14B
    if SET == "users":
        chosen = USERS
    if SET.startswith("only:"):
        chosen = [i for i in ERC4626 + STRONG if i[0] == SET[5:]]
    invs = [{"id": i, "statement": s, "assert": a} for i, s, a in chosen]
    if name == "OZVault" and SET in ("standard", "strong"):
        invs.append({"id": "needs_repair", "statement": "Total assets are never negative",
                     "assert": "assertEq(target.nope(), 0);"})
    return {"constructor": CTOR[name], "invariants": invs}


class H(http.server.BaseHTTPRequestHandler):
    def do_POST(self):
        body = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
        prompt = body["prompt"]
        if "does not compile" in prompt:
            answer = {"assert": "assertLe(target.totalSupply(), handler.sumBalanceOf());"}
        elif "can never fail" in prompt:
            wanted = int(re.search(r"Propose up to (\d+)", prompt).group(1))
            batch = REPLACE_2 if "still_non_negative" in prompt else REPLACE_1
            answer = {"invariants": [{"id": i, "statement": s, "assert": a}
                                     for i, s, a in batch[:wanted]]}
        else:
            name = re.search(r"Contract: (\w+) \(", prompt).group(1)
            answer = plan_for(name)
        if DUMP:
            kind = ("repair" if "does not compile" in prompt
                    else "replace" if "can never fail" in prompt else "plan")
            m = re.search(r"Contract: (\w+) \(", prompt)
            with open(f"{DUMP}/{m.group(1) if m else 'unknown'}-{kind}.txt", "w") as f:
                f.write(prompt)
        with open(LOG, "a") as f:
            f.write(json.dumps({"format": body.get("format"), "num_ctx": body["options"]["num_ctx"],
                                "kind": ("repair" if "does not compile" in prompt
                                         else "replace" if "can never fail" in prompt else "plan"),
                                "prompt_chars": len(prompt)}) + "\n")
        out = json.dumps({"response": json.dumps(answer)}).encode()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(out)))
        self.end_headers()
        self.wfile.write(out)

    def log_message(self, *a):
        pass


http.server.HTTPServer(("127.0.0.1", PORT), H).serve_forever()
