use stellar_xdr::*;

#[cfg(feature = "std")]
#[test]
fn test_build_small_tx_with_std() -> Result<(), Error> {
    let te = TransactionEnvelope::EnvelopeTypeTx(TransactionV1Envelope {
        tx: Transaction {
            source_account: MuxedAccount::KeyTypeEd25519(Uint256([0; 32])),
            fee: 0,
            seq_num: SequenceNumber(1),
            cond: Preconditions::PrecondNone,
            memo: Memo::MemoText("Stellar".as_bytes().try_into()?),
            operations: [].to_vec().try_into()?,
            ext: TransactionExt::V0,
        },
        signatures: [].try_into()?,
    });
    let xdr = te.to_xdr_base64()?;
    assert_eq!(xdr, "AAAAAgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAAAAAAAAABAAAAB1N0ZWxsYXIAAAAAAAAAAAAAAAAA");
    Ok(())
}

#[cfg(feature = "alloc")]
#[test]
fn test_build_small_tx_with_alloc() -> Result<(), Error> {
    let _ = TransactionEnvelope::EnvelopeTypeTx(TransactionV1Envelope {
        tx: Transaction {
            source_account: MuxedAccount::KeyTypeEd25519(Uint256([0; 32])),
            fee: 0,
            seq_num: SequenceNumber(1),
            cond: Preconditions::PrecondNone,
            memo: Memo::MemoText("Stellar".as_bytes().try_into()?),
            operations: [].to_vec().try_into()?,
            ext: TransactionExt::V0,
        },
        signatures: [].try_into()?,
    });
    Ok(())
}

#[cfg(not(feature = "alloc"))]
#[test]
fn test_build_small_tx_with_alloc() -> Result<(), Error> {
    let _ = TransactionEnvelope::EnvelopeTypeTx(TransactionV1Envelope {
        tx: Transaction {
            source_account: MuxedAccount::KeyTypeEd25519(Uint256([0; 32])),
            fee: 0,
            seq_num: SequenceNumber(1),
            cond: Preconditions::PrecondNone,
            memo: Memo::MemoText("Stellar".as_bytes().try_into()?),
            operations: (&[]).try_into()?,
            ext: TransactionExt::V0,
        },
        signatures: (&[]).try_into()?,
    });
    Ok(())
}
