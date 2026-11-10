// Adapted from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/verifier/src/lib.rs: its
// errors and the announced shape. MIT OR Apache-2.0; see AGENTS.md.
//! The Keccak VM's statement (leanVM 9d50c92a3) and the verifier pieces built on it, generic over the scalar they
//! compute on, shared by `leanvm_univariate` (π1) and `leanvm_rec` (π2). See `README.md`.
//!
//! - [`layout`]: the VM's six instruction tables (leanVM 42422001's five and the `SHA3` table), their bus flushes and
//!   constraints.
//! - [`flock`], [`flock_min`], [`ring_tower`]: Flock's verifier (zerocheck with a univariate skip, lincheck, ring
//!   switch); [`keccak_flock`]: the Keccak-f block and its structured terminal.
//! - [`transcript`]: the Keccak-256 Fiat–Shamir chain ([`transcript::KeccakChannel`], [`transcript::KeccakWriter`]).
//! - [`evm`]: the recorder that runs a verifier on a symbolic scalar, the nodes' code for `evm_link`, and a revm
//!   machine with `FIELD_MUL` and EIP-8141's frame introspection over a frame of PCS claims.
//! - [`shapes`]: the measured workloads (the reference: 128 signatures) and the program's IV.

#![forbid(unsafe_code)]

pub mod evm;
pub mod field;
pub mod flock;
pub mod flock_min;
pub mod keccak_flock;
pub mod layout;
pub mod multilinear;
pub mod ring_tower;
pub mod scalar;
pub mod shapes;
pub mod transcript;

pub use field::{E, K};
pub use layout::{N_TABLES, TABLE_NAMES};

/// Why a proof was rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifierError {
    FieldElementLength,
    DigestHalf,
    MultilinearSize,
    NotPowerOfTwo,
    StreamNotWholeElements,
    StreamExhausted,
    GrindingNonce,
    MerkleOpeningMissing,
    MerkleOpeningShape,
    MerkleRootMismatch,
    StreamNotConsumed,
    MerkleNotConsumed,
    /// The GKR layer whose children do not match its sumcheck.
    GkrLayer(usize),
    BusCountZero,
    TableSumcheckTerminal,
    AnnouncedTableSizes,
    WhirShape,
    QueryCountLadder,
    InducedBasisDimensions,
    WhirTerminal,
    WhirNoTerminalLevel,
    FlockLincheckTerminal,
    AnnouncedHighLimb,
    PcsInverseRate,
    CommittedSize,
    /// New here: the announced sizes are not the shape the verifier was built for.
    AnnouncedShape,
    /// New here: Flock's lincheck terminal does not close.
    FlockMatrixTerminal,
    /// New here: the stack claims' batching sumcheck does not close.
    StackBatchTerminal,
    /// New here (`crates/leanvm/univariate`): an announced table row count exceeds its height's `2^r`.
    TableRows,
    /// New here (`crates/leanvm/univariate`): a shape the verifier cannot be built for (a height below 2).
    InvalidShape,
    /// New here (`crates/leanvm/rec`, π2): a denominator of π2's verifier vanishes at its challenges.
    RecDegenerate,
}

impl std::fmt::Display for VerifierError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for VerifierError {}

fn require(condition: bool, error: VerifierError) -> Result<(), VerifierError> {
    if condition { Ok(()) } else { Err(error) }
}

/// What the announced sizes are: the memory's log size, each table's rows and WHIR's log inverse rate; and the
/// stacked bytecode's length, which the program fixes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    pub log_memory: u64,
    pub table_rows: [u64; N_TABLES],
    pub log_inv_rate: u64,
    pub bytecode_len: usize,
}
