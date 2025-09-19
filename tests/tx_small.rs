#![cfg(all(
    any(feature = "curr", feature = "next"),
    not(all(feature = "curr", feature = "next"))
))]

#[cfg(feature = "curr")]
use stellar_xdr::curr as stellar_xdr;
#[cfg(feature = "next")]
use stellar_xdr::next as stellar_xdr;

use stellar_xdr::{
    Error, Memo, MuxedAccount, Preconditions, SequenceNumber, Transaction, TransactionEnvelope,
    TransactionExt, TransactionV1Envelope, Uint256,
};

#[cfg(feature = "alloc")]
#[test]
fn test_build_small_tx_with_alloc() -> Result<(), Error> {
    let _tx = TransactionEnvelope::Tx(TransactionV1Envelope {
        tx: Transaction {
            source_account: MuxedAccount::Ed25519(Uint256([0; 32])),
            fee: 0,
            seq_num: SequenceNumber(1),
            cond: Preconditions::None,
            memo: Memo::Text("Stellar".as_bytes().try_into()?),
            operations: [].to_vec().try_into()?,
            ext: TransactionExt::V0,
        },
        signatures: [].try_into()?,
    });
    Ok(())
}

#[cfg(feature = "alloc")]
#[test]
fn convert_reference_of_tx_to_unsigned_transaction_envelope() -> Result<(), Error> {
    let tx = &Transaction {
        source_account: MuxedAccount::Ed25519(Uint256([0; 32])),
        fee: 0,
        seq_num: SequenceNumber(1),
        cond: Preconditions::None,
        memo: Memo::Text("Stellar".as_bytes().try_into()?),
        operations: [].to_vec().try_into()?,
        ext: TransactionExt::V0,
    };
    let _: TransactionEnvelope = tx.into();
    Ok(())
}

#[cfg(not(feature = "alloc"))]
#[test]
fn test_build_small_tx_with_alloc() -> Result<(), Error> {
    let _tx = TransactionEnvelope::Tx(TransactionV1Envelope {
        tx: Transaction {
            source_account: MuxedAccount::Ed25519(Uint256([0; 32])),
            fee: 0,
            seq_num: SequenceNumber(1),
            cond: Preconditions::None,
            memo: Memo::Text("Stellar".as_bytes().try_into()?),
            operations: (&[]).try_into()?,
            ext: TransactionExt::V0,
        },
        signatures: (&[]).try_into()?,
    });
    Ok(())
}
