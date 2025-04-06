tolk 0.10

import "@stdlib/tvm-dicts"
import "@stdlib/gas-payments"



const `error::signature_disabled` = 132;
const `error::invalid_seqno` = 133;
const `error::invalid_wallet_id` = 134;
const `error::invalid_signature` = 135;
const `error::expired` = 136;
const `error::external_send_message_must_have_ignore_errors_send_mode` = 137;
const `error::invalid_message_operation` = 138;
const `error::add_extension` = 139;
const `error::remove_extension` = 140;
const `error::unsupported_action` = 141;
const `error::disable_signature_when_extensions_is_empty` = 142;
const `error::this_signature_mode_already_set` = 143;
const `error::remove_last_extension_when_signature_disabled` = 144;
const `error::extension_wrong_workchain` = 145;
const `error::only_extension_can_change_signature_mode` = 146;
const `error::invalid_c5` = 147;

const `size::bool` = 1;
const `size::seqno` = 32;
const `size::wallet_id` = 32;
const `size::public_key` = 256;
const `size::valid_until` = 32;
const `size::message_flags` = 4;
const `size::signature` = 512;
const `size::message_operation_prefix` = 32;
const `size::address_hash_size` = 256;
const `size::query_id` = 64;

const `prefix::signed_external` = 0x7369676E;
const `prefix::signed_internal` = 0x73696E74;
const `prefix::extension_action` = 0x6578746E;

fun checkAndRemoveAddExtensionPrefix(mutate self: slice): bool
    asm "x{02} SDBEGINSQ";
fun checkAndRemoveRemoveExtensionPrefix(mutate self: slice): bool 
    asm "x{03} SDBEGINSQ";
fun checkAndRemoveSetSignatureAllowedPrefix(mutate self: slice): bool
    asm "x{04} SDBEGINSQ";

/// returns the number of trailing zeroes in slice s.
@pure
fun countTrailingZeroes(s: slice): int
    asm "SDCNTTRAIL0";

// `action_send_msg` has 0x0ec3c86d prefix
// https://github.com/ton-blockchain/ton/blob/5c392e0f2d946877bb79a09ed35068f7b0bd333a/crypto/block/block.tlb#L380
fun enforceAndRemoveActionSendMsgPrefix(mutate self: slice): void
    asm "x{0ec3c86d} SDBEGINS";

/// put raw list of OutActions to C5 register.
/// OutList TLB-schema - https://github.com/ton-blockchain/ton/blob/5c392e0f2d946877bb79a09ed35068f7b0bd333a/crypto/block/block.tlb#L378
/// C5 register - https://docs.ton.org/tvm.pdf, page 11
fun setC5Actions(actionList: cell): void
    asm "c5 POP";

/// transforms an ordinary or exotic cell into a Slice, as if it were an ordinary cell. A flag is returned indicating whether c is exotic. If that be the case, its type can later be deserialized from the first eight bits of s.
@pure
fun beginParseRaw(c: cell): (slice, int)
    asm "XCTOS";

@inline
fun verifyC5Actions(c5: cell, isExternal: bool): cell {
  // XCTOS doesn't automatically load exotic cells (unlike CTOS `begin_parse`).
  // we use it in `verify_c5_actions` because during action phase processing exotic cells in c5 won't be unfolded too.
  // exotic cell starts with 0x02, 0x03 or 0x04 so it will not pass action_send_msg prefix check
  var (cs: slice, _) = c5.beginParseRaw();

  var count: int = 0;

  while (!cs.isEndOfSlice()) {
    // only `action_send_msg` is allowed; `action_set_code`, `action_reserve_currency` or `action_change_library` are not.
    cs.enforceAndRemoveActionSendMsgPrefix();

    assert(cs.getRemainingBitsCount() == 8) throw `error::invalid_c5`; // send_mode
    assert(cs.getRemainingRefsCount() == 2) throw `error::invalid_c5`; // next-action-ref and MessageRelaxed ref

    // enforce that send_mode has +2 bit (ignore errors) set for external message.
    // if such send_mode is not set and sending fails at the action phase (for example due to insufficient balance) then the seqno will not be increased and the external message will be processed again and again.

    // action_send_msg#0ec3c86d mode:(## 8) out_msg:^(MessageRelaxed Any) = OutAction;
    // https://github.com/ton-blockchain/ton/blob/5c392e0f2d946877bb79a09ed35068f7b0bd333a/crypto/block/block.tlb#L380
    // load 7 bits and make sure that they end with 1
    assert(!(isExternal && (countTrailingZeroes(cs.preloadBits(7)) > 0))) throw `error::external_send_message_must_have_ignore_errors_send_mode`;

    (cs, _) = cs.preloadRef().beginParseRaw();
    count += 1;
  }
  assert(count <= 255) throw `error::invalid_c5`;
  assert(cs.getRemainingRefsCount() == 0) throw `error::invalid_c5`;

  return c5;
}

@inline_ref
fun processActions(cs: slice, isExternal: bool, isExtension: bool) {
  var c5Actions: cell? = cs.loadMaybeRef();
  if (c5Actions != null) {
    // Simply set the C5 register with all pre-computed actions after verification:
    setC5Actions(c5Actions.verifyC5Actions(isExternal));
  }
  if (cs.loadInt(1) == 0) { // has_other_actions
    return;
  }

  // Loop extended actions until we reach standard actions
  while (true) {
    var isAddExtension: bool = cs.checkAndRemoveAddExtensionPrefix();
    var isRemoveExtension: bool = isAddExtension ? false : cs.checkAndRemoveRemoveExtensionPrefix();
    // Add/remove extensions
    if (isAddExtension || isRemoveExtension) {
      var (addressWc: int, addressHash: int) = parseStandardAddress(cs.loadAddress());
      var (myAddressWc: int, _) = parseStandardAddress(getMyAddress());

      assert(myAddressWc == addressWc) throw `error::extension_wrong_workchain`;

      var dataSlice: slice = getContractData().beginParse();
      var dataSliceBeforeExtensions: slice = dataSlice.loadBits(`size::bool` + `size::seqno` + `size::wallet_id` + `size::public_key`);
      var extensions: cell? = dataSlice.preloadDict();

      // Add extension
      if (isAddExtension) {
        var isSuccess: bool = extensions.uDictSetBuilderIfNotExists(`size::address_hash_size`, addressHash, beginCell().storeInt(-1, 1));
        assert(isSuccess) throw `error::add_extension`;
      } else { // Remove extension
        var isSuccess: bool = extensions.uDictDelete(`size::address_hash_size`, addressHash);
        assert(isSuccess) throw `error::remove_extension`;
        var isSignatureAllowed: int = dataSliceBeforeExtensions.preloadInt(`size::bool`);
        assert(!((extensions == null) && (!isSignatureAllowed))) throw `error::remove_last_extension_when_signature_disabled`;
      }

      setContractData(beginCell()
              .storeSlice(dataSliceBeforeExtensions)
              .storeDict(extensions)
              .endCell());

    } else if (cs.checkAndRemoveSetSignatureAllowedPrefix()) {
      assert(isExtension) throw `error::only_extension_can_change_signature_mode`;
      var allowSignature: bool = cs.loadBool();
      var dataSlice: slice = getContractData().beginParse();
      var isSignatureAllowed: bool = dataSlice.loadBool();
      assert(!(isSignatureAllowed == allowSignature)) throw `error::this_signature_mode_already_set`;
      isSignatureAllowed = allowSignature;

      var dataTail: slice = dataSlice; // seqno, wallet_id, public_key, extensions
      if (!allowSignature) { // disallow
        var isExtensionsNotEmpty: int = dataSlice.skipBits(`size::seqno` + `size::wallet_id` + `size::public_key`).preloadInt(1);
        assert(isExtensionsNotEmpty) throw `error::disable_signature_when_extensions_is_empty`;
      }

      setContractData(beginCell()
        .storeBool(isSignatureAllowed)
        .storeSlice(dataTail) // seqno, wallet_id, public_key, extensions
        .endCell());
    } else {
      throw `error::unsupported_action`;
    }
    if (!cs.getRemainingRefsCount()) {
      return;
    }
    cs = cs.preloadRef().beginParse();
  }
}

// ------------------------------------------------------------------------------------------------

@inline
fun processSignedRequest(inMsgBody: slice, isExternal: bool) {
  var signature: slice = inMsgBody.getLastBits(`size::signature`);
  var signedSlice: slice = inMsgBody.removeLastBits(`size::signature`);

  var cs: slice = signedSlice;
  cs.skipBits(`size::message_operation_prefix`); // skip signed_internal or signed_external prefix
  var (walletId: int, validUntil: int, seqno: int) = (cs.loadUint(`size::wallet_id`), cs.loadUint(`size::valid_until`), cs.loadUint(`size::seqno`));

  var dataSlice: slice = getContractData().beginParse();
  var isSignatureAllowed: bool = dataSlice.loadBool();
  var storedSeqno: int = dataSlice.loadUint(`size::seqno`);
  var dataTail: slice = dataSlice; // wallet_id, public_key, extensions
  var storedWalletId: int = dataSlice.loadUint(`size::wallet_id`);
  var publicKey: int = dataSlice.loadUint(`size::public_key`);
  var isExtensionsNotEmpty: bool = dataSlice.loadBool();

  var signatureRes: bool = isSignatureValid(sliceHash(signedSlice), signature, publicKey);
  if (!signatureRes) {
    if (isExternal) {
      throw `error::invalid_signature`;
    } else {
      return;
    }
  }
  assert(!((!isSignatureAllowed) && isExtensionsNotEmpty)) throw `error::signature_disabled`;
  assert(seqno == storedSeqno) throw `error::invalid_seqno`;
  assert(walletId == storedWalletId) throw `error::invalid_wallet_id`;
  assert(validUntil > now()) throw `error::expired`;

  if (isExternal) {
    acceptExternalMessage();
  }

  // Store and commit the seqno increment to prevent replays even if the subsequent requests fail.
  storedSeqno = storedSeqno + 1;
  setContractData(beginCell()
    .storeBool(true) // is_signature_allowed
    .storeUint(storedSeqno, `size::seqno`)
    .storeSlice(dataTail) // wallet_id, public_key, extensions
    .endCell());

  if (isExternal) {
    commitContractDataAndActions();
  }

  processActions(cs, isExternal, false);
}

@inline
fun onExternalMessage(inMsgBody: slice) {
  assert(inMsgBody.preloadUint(`size::message_operation_prefix`) == `prefix::signed_external`) throw `error::invalid_message_operation`;
  processSignedRequest(inMsgBody, true);
}

// ------------------------------------------------------------------------------------------------

@inline
fun onInternalMessage(inMsgFull: cell, inMsgBody: slice) {
  if (inMsgBody.getRemainingBitsCount() < `size::message_operation_prefix`) {
    return;
  }
  var op: int = inMsgBody.preloadUint(`size::message_operation_prefix`);
  if ((op != `prefix::extension_action`) && (op != `prefix::signed_internal`)) {
    return;
  }

  // bounded messages has 0xffffff prefix and skipped by op check

  if (op == `prefix::extension_action`) {
    inMsgBody.skipBits(`size::message_operation_prefix`);

    var inMsgFullSlice: slice = inMsgFull.beginParse();
    inMsgFullSlice.skipBits(`size::message_flags`);
    // Authenticate extension by its address.
    var (senderAddressWc: int, senderAddressHash: int) = parseStandardAddress(inMsgFullSlice.loadAddress());
    var (myAddressWc: int, _) = parseStandardAddress(getMyAddress());

    if (myAddressWc != senderAddressWc) {
      return;
    }

    var extensions: cell? = getContractData().beginParse()
      .skipBits(`size::bool` + `size::seqno` + `size::wallet_id` + `size::public_key`)
      .preloadDict();

    // Note that some random contract may have deposited funds with this prefix,
    // so we accept the funds silently instead of throwing an error (wallet v4 does the same).
    var (_, extensionFound: bool) = extensions.uDictGet(`size::address_hash_size`, senderAddressHash);
    if (!extensionFound) {
      return;
    }

    inMsgBody.skipBits(`size::query_id`); // skip query_id

    processActions(inMsgBody, false, true);
    return;

  }

  // Additional check to make sure that there are enough bits for reading before signature check
  if (inMsgBody.getRemainingBitsCount() < `size::message_operation_prefix` + `size::wallet_id` + `size::valid_until` + `size::seqno` + `size::signature`) {
    return;
  }
  processSignedRequest(inMsgBody, false);
}

// ------------------------------------------------------------------------------------------------
// Get methods

get is_signature_allowed(): int {
  return getContractData().beginParse()
    .preloadInt(`size::bool`);
}

get seqno(): int {
  return getContractData().beginParse()
    .skipBits(`size::bool`)
    .preloadUint(`size::seqno`);
}

get get_subwallet_id(): int {
  return getContractData().beginParse()
    .skipBits(`size::bool` + `size::seqno`)
    .preloadUint(`size::wallet_id`);
}

get get_public_key(): int {
  return getContractData().beginParse()
    .skipBits(`size::bool` + `size::seqno` + `size::wallet_id`)
    .preloadUint(`size::public_key`);
}

// Returns raw dictionary (or null if empty) where keys are address hashes. Workchains of extensions are same with wallet smart contract workchain
get get_extensions(): cell? {
  return getContractData().beginParse()
    .skipBits(`size::bool` + `size::seqno` + `size::wallet_id` + `size::public_key`)
    .preloadDict();
}
