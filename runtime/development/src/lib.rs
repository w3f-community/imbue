// Copyright 2019-2021 Parity Technologies (UK) Ltd.
// This file is part of Cumulus.

// Cumulus is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Cumulus is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Cumulus.  If not, see <http://www.gnu.org/licenses/>.

#![cfg_attr(not(feature = "std"), no_std)]
// `construct_runtime!` does a lot of recursion and requires us to increase the limit to 256.
#![recursion_limit = "256"]

// Make the WASM binary available.
#[cfg(feature = "std")]
include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));

use sp_api::impl_runtime_apis;

use sp_core::{
	crypto::KeyTypeId,
	u32_trait::{_1, _2, _3, _4, _5},
	OpaqueMetadata,
};
use smallvec::smallvec;
use sp_runtime::{
	generic::Era,
	curve::PiecewiseLinear,
	create_runtime_str, generic, impl_opaque_keys,
	traits::{AccountIdLookup, BlakeTwo256, Block as BlockT, Verify, Extrinsic as ExtrinsicT, ConvertInto, OpaqueKeys},
	transaction_validity::{TransactionPriority, TransactionSource, TransactionValidity},
	ApplyExtrinsicResult,Perbill,Percent,Permill,Perquintill
};

use sp_std::{marker::PhantomData, prelude::*};
use sp_staking::SessionIndex;

#[cfg(feature = "std")]
use sp_version::NativeVersion;
use sp_version::RuntimeVersion;

// Weights used in the runtime
mod weights;

// A few exports that help ease life for downstream crates.
pub use frame_support::{
	ensure,
	construct_runtime, match_type, parameter_types,
	traits::{Contains,Currency, Everything, IsInVec,KeyOwnerProofSystem, OnUnbalanced, Randomness,U128CurrencyToVote,CurrencyToVote },
	weights::{
		constants::{BlockExecutionWeight, ExtrinsicBaseWeight, RocksDbWeight, WEIGHT_PER_SECOND},
		DispatchClass, IdentityFee, Weight,WeightToFeePolynomial,WeightToFeeCoefficient, WeightToFeeCoefficients,
	},PalletId,
	StorageValue,
};
use frame_system::{
	limits::{BlockLength, BlockWeights},
	EnsureOneOf, EnsureRoot,EnsureSigned
};
pub use pallet_balances::Call as BalancesCall;
pub use pallet_timestamp::Call as TimestampCall;



// use pallet_collective::{EnsureMember, EnsureProportionAtLeast, EnsureProportionMoreThan};
pub use sp_consensus_aura::sr25519::AuthorityId as AuraId;
use crate::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::Encode;
// use pallet_grandpa::{
// 	fg_primitives, AuthorityId as GrandpaId, AuthorityList as GrandpaAuthorityList,
// };
// use pallet_im_online::sr25519::AuthorityId as ImOnlineId;
use primitives::v1::{
	AccountId, AccountIndex, Balance, BlockNumber, CandidateEvent, CommittedCandidateReceipt,
	CoreState, GroupRotationInfo, Hash, Id as ParaId, InboundDownwardMessage, InboundHrmpMessage,
	Moment, Nonce, OccupiedCoreAssumption, PersistedValidationData, ScrapedOnChainVotes,
	SessionInfo, Signature, ValidationCode, ValidationCodeHash, ValidatorId, ValidatorIndex,
};
use parachains_common::{
	impls::{AssetsFrom, NonZeroIssuance},
	AssetId,
};

use xcm_builder::{AsPrefixedGeneralIndex, ConvertedConcreteAssetId, FungiblesAdapter};
use xcm_executor::{Config,traits::{JustTry, ShouldExecute}, XcmExecutor};

// XCM imports
use pallet_xcm::{EnsureXcm, IsMajorityOfBody, XcmPassthrough};
use pallet_session::historical as session_historical;

use polkadot_parachain::primitives::Sibling;
use xcm::latest::prelude::*;
use xcm_builder::{
	AccountId32Aliases, CurrencyAdapter,
	EnsureXcmOrigin, FixedWeightBounds, IsConcrete, LocationInverter, NativeAsset,
	ParentAsSuperuser, ParentIsDefault, RelayChainAsNative, SiblingParachainAsNative,
	SiblingParachainConvertsVia, SignedAccountId32AsNative, SignedToAccountId32,
	SovereignSignedViaLocation, TakeWeightCredit, UsingComponents,
};

/// common types for the runtime.
pub use runtime_common::*;
pub use runtime_common::Index;

/// Implementations of some helper traits passed into runtime modules as associated types.
pub mod impls;
use impls::Author;

pub type SessionHandlers = ();

/// Handles converting a weight scalar to a fee value, based on the scale and granularity of the
/// node's balance type.
///
/// This should typically create a mapping between the following ranges:
///   - `[0, MAXIMUM_BLOCK_WEIGHT]`
///   - `[Balance::min, Balance::max]`
///
/// Yet, it can be used for any other sort of change to weight-fee. Some examples being:
///   - Setting it to `0` will essentially disable the weight fee.
///   - Setting it to `1` will cause the literal `#[weight = x]` values to be charged.
pub struct WeightToFee;
impl WeightToFeePolynomial for WeightToFee {
	type Balance = Balance;
	fn polynomial() -> WeightToFeeCoefficients<Self::Balance> {
		// in Rococo, extrinsic base weight (smallest non-zero weight) is mapped to 1 MILLIUNIT:
		// in our template, we map to 1/10 of that, or 1/10 MILLIUNIT
		let p = MILLI_IMBU / 10;
		let q = 100 * Balance::from(ExtrinsicBaseWeight::get());
		smallvec![WeightToFeeCoefficient {
			degree: 1,
			negative: false,
			coeff_frac: Perbill::from_rational(p % q, q),
			coeff_integer: p / q,
		}]
	}
}

/// Opaque types. These are used by the CLI to instantiate machinery that don't need to know
/// the specifics of the runtime. They can then be made to be agnostic over specific formats
/// of data like extrinsics, allowing for them to continue syncing the network through upgrades
/// to even the core data structures.
pub mod opaque {
	use super::*;
	use sp_runtime::{generic, traits::BlakeTwo256};

	pub use sp_runtime::OpaqueExtrinsic as UncheckedExtrinsic;
	/// Opaque block header type.
	pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
	/// Opaque block type.
	pub type Block = generic::Block<Header, UncheckedExtrinsic>;
	/// Opaque block identifier type.
	pub type BlockId = generic::BlockId<Block>;
}

impl_opaque_keys! {
	pub struct SessionKeys {
		pub aura: Aura,
	}
}

/// This runtime version.
#[sp_version::runtime_version]
pub const VERSION: RuntimeVersion = RuntimeVersion {
	spec_name: create_runtime_str!("imbue-dev"),
	impl_name: create_runtime_str!("imbue-dev"),
	authoring_version: 1,
	spec_version: 1001,
	impl_version: 1,
	apis: RUNTIME_API_VERSIONS,
	transaction_version: 1,
};

/// The version information used to identify this runtime when compiled natively.
#[cfg(feature = "std")]
pub fn native_version() -> NativeVersion {
	NativeVersion { runtime_version: VERSION, can_author_with: Default::default() }
}

type MoreThanHalfCouncil = EnsureOneOf<
	AccountId,
	EnsureRoot<AccountId>,
	pallet_collective::EnsureProportionMoreThan<_1, _2, AccountId, CouncilCollective>,
>;

/// We allow `Normal` extrinsics to fill up the block up to 75%, the rest can be used
/// by  Operational  extrinsics.
/// We allow for .5 seconds of compute with a 12 second average block time.
const MAXIMUM_BLOCK_WEIGHT: Weight = WEIGHT_PER_SECOND / 2;

pub type SignedPayload = generic::SignedPayload<Call, SignedExtra>;

parameter_types! {
	pub const BlockHashCount: BlockNumber = 250;
	pub const Version: RuntimeVersion = VERSION;
	pub RuntimeBlockLength: BlockLength =
		BlockLength::max_with_normal_ratio(5 * 1024 * 1024, NORMAL_DISPATCH_RATIO);
	pub RuntimeBlockWeights: BlockWeights = BlockWeights::builder()
		.base_block(BlockExecutionWeight::get())
		.for_class(DispatchClass::all(), |weights| {
			weights.base_extrinsic = ExtrinsicBaseWeight::get();
		})
		.for_class(DispatchClass::Normal, |weights| {
			weights.max_total = Some(NORMAL_DISPATCH_RATIO * MAXIMUM_BLOCK_WEIGHT);
		})
		.for_class(DispatchClass::Operational, |weights| {
			weights.max_total = Some(MAXIMUM_BLOCK_WEIGHT);
			// Operational transactions have some extra reserved space, so that they
			// are included even if block reached `MAXIMUM_BLOCK_WEIGHT`.
			weights.reserved = Some(
				MAXIMUM_BLOCK_WEIGHT - NORMAL_DISPATCH_RATIO * MAXIMUM_BLOCK_WEIGHT
			);
		})
		.avg_block_initialization(AVERAGE_ON_INITIALIZE_RATIO)
		.build_or_panic();
	pub const SS58Prefix: u8 = 42;
}

impl frame_system::Config for Runtime {
	/// The identifier used to distinguish between accounts.
	type AccountId = AccountId;
	/// The aggregated dispatch type that is available for extrinsics.
	type Call = Call;
	/// The lookup mechanism to get account ID from whatever is passed in dispatchers.
	type Lookup = AccountIdLookup<AccountId, ()>;
	/// The index type for storing how many extrinsics an account has signed.
	type Index = runtime_common::Index;	
	/// The index type for blocks.
	type BlockNumber = BlockNumber;
	type Hash = Hash;

	/// The hashing algorithm used.
	type Hashing = BlakeTwo256;
	/// The header type.
	type Header = generic::Header<BlockNumber, BlakeTwo256>;
	/// The ubiquitous event type.
	type Event = Event;
	/// The ubiquitous origin type.
	type Origin = Origin;
	/// Maximum number of block number to block hash mappings to keep (oldest pruned first).
	type BlockHashCount = BlockHashCount;
	/// Runtime version.
	type Version = Version;
	/// Converts a module to an index of this module in the runtime.
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type DbWeight = ();
	type BaseCallFilter = frame_support::traits::Everything;
	type SystemWeightInfo = ();
	type BlockWeights = RuntimeBlockWeights;
	type BlockLength = RuntimeBlockLength;
	type SS58Prefix = SS58Prefix;
	type OnSetCode = cumulus_pallet_parachain_system::ParachainSetCode<Self>;
}

parameter_types! {
	pub const MinimumPeriod: u64 = SLOT_DURATION / 2;
}

impl pallet_timestamp::Config for Runtime {
	/// A timestamp: milliseconds since the unix epoch.
	type Moment = u64;
	type OnTimestampSet = ();
	type MinimumPeriod = MinimumPeriod;
	type WeightInfo = ();
}

parameter_types! {
	pub const ExistentialDeposit: Balance = 1 * MICRO_IMBU;
	pub const TransferFee: Balance = 1 * MICRO_IMBU;
	pub const CreationFee: Balance = 1 * MICRO_IMBU;
	pub const TransactionByteFee: Balance = 1 * (MICRO_IMBU / 100);
	pub const MaxLocks: u32 = 50;
	pub const MaxReserves: u32 = 50;
}

impl pallet_balances::Config for Runtime {
	/// The type for recording an account's balance.
	type Balance = Balance;
	/// The ubiquitous event type.
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = MaxLocks;
	type MaxReserves = MaxReserves;
	type ReserveIdentifier = [u8; 8];
}

// impl pallet_grandpa::Config for Runtime {
// 	type Event = Event;
// 	type Call = Call;

// 	type KeyOwnerProof =
// 		<Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(KeyTypeId, GrandpaId)>>::Proof;

// 	type KeyOwnerIdentification = <Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(
// 		KeyTypeId,
// 		GrandpaId,
// 	)>>::IdentificationTuple;

// 	type KeyOwnerProofSystem = Historical;

// 	type HandleEquivocation = pallet_grandpa::EquivocationHandler<
// 		Self::KeyOwnerIdentification,
// 		Offences,
// 		ReportLongevity,
// 	>;

// 	type WeightInfo = ();
// 	type MaxAuthorities = MaxAuthorities;
// }

impl pallet_randomness_collective_flip::Config for Runtime {}

type NegativeImbalance = <Balances as Currency<AccountId>>::NegativeImbalance;

pub struct DealWithFees;
impl OnUnbalanced<NegativeImbalance> for DealWithFees {
	fn on_unbalanceds<B>(mut fees_then_tips: impl Iterator<Item = NegativeImbalance>) {
		if let Some(fees) = fees_then_tips.next() {
			// for fees, 80% to treasury, 20% to author
			let mut split = fees.ration(80, 20);
			if let Some(tips) = fees_then_tips.next() {
				// for tips, if any, 80% to treasury, 20% to author (though this can be anything)
				tips.ration_merge_into(80, 20, &mut split);
			}
			Treasury::on_unbalanced(split.0);
			Author::on_unbalanced(split.1);
		}
	}
}

parameter_types! {
	pub const OperationalFeeMultiplier: u8 = 5;
}

impl pallet_transaction_payment::Config for Runtime {
	type OnChargeTransaction = pallet_transaction_payment::CurrencyAdapter<Balances,DealWithFees>;
	type TransactionByteFee = TransactionByteFee;
	type WeightToFee = IdentityFee<Balance>;
	type FeeMultiplierUpdate = ();
	type OperationalFeeMultiplier = OperationalFeeMultiplier;
}

impl pallet_sudo::Config for Runtime {
	type Call = Call;
	type Event = Event;
}

parameter_types! {
	pub const ReservedXcmpWeight: Weight = MAXIMUM_BLOCK_WEIGHT / 4;
	pub const ReservedDmpWeight: Weight = MAXIMUM_BLOCK_WEIGHT / 4;
}

impl cumulus_pallet_parachain_system::Config for Runtime {
	type Event = Event;
	type OnValidationData = ();
	type SelfParaId = parachain_info::Pallet<Runtime>;
	type OutboundXcmpMessageSource = XcmpQueue;
	type DmpMessageHandler = DmpQueue;
	type ReservedDmpWeight = ReservedDmpWeight;
	type XcmpMessageHandler = XcmpQueue;
	type ReservedXcmpWeight = ReservedXcmpWeight;
}

impl parachain_info::Config for Runtime {}

impl cumulus_pallet_aura_ext::Config for Runtime {}


parameter_types! {
	pub IgnoredIssuance: Balance = Treasury::pot();
	pub const QueueCount: u32 = 300;
	pub const MaxQueueLen: u32 = 1000;
	pub const FifoQueueLen: u32 = 250;
	pub const GiltPeriod: BlockNumber = 30 * DAYS;
	pub const MinFreeze: Balance = 10_000 * CENTI_IMBU;
	pub const IntakePeriod: BlockNumber = 5 * MINUTES;
	pub const MaxIntakeBids: u32 = 100;
}

// impl pallet_gilt::Config for Runtime {
// 	type Event = Event;
// 	type Currency = Balances;
// 	type CurrencyBalance = Balance;
// 	type AdminOrigin = MoreThanHalfCouncil;
// 	type Deficit = (); // Mint
// 	type Surplus = (); // Burn
// 	type IgnoredIssuance = IgnoredIssuance;
// 	type QueueCount = QueueCount;
// 	type MaxQueueLen = MaxQueueLen;
// 	type FifoQueueLen = FifoQueueLen;
// 	type Period = GiltPeriod;
// 	type MinFreeze = MinFreeze;
// 	type IntakePeriod = IntakePeriod;
// 	type MaxIntakeBids = MaxIntakeBids;
// 	type WeightInfo = weights::pallet_gilt::WeightInfo<Runtime>;
// }

parameter_types! {
	pub const RocLocation: MultiLocation = MultiLocation::parent();
	pub const RococoNetwork: NetworkId = NetworkId::Polkadot;
	pub RelayChainOrigin: Origin = cumulus_pallet_xcm::Origin::Relay.into();
	pub Ancestry: MultiLocation = Parachain(ParachainInfo::parachain_id().into()).into();
	pub CheckingAccount: AccountId = PolkadotXcm::check_account();
}

/// Type for specifying how a `MultiLocation` can be converted into an `AccountId`. This is used
/// when determining ownership of accounts for asset transacting and when attempting to use XCM
/// `Transact` in order to determine the dispatch Origin.
pub type LocationToAccountId = (
	// The parent (Relay-chain) origin converts to the default `AccountId`.
	ParentIsDefault<AccountId>,
	// Sibling parachain origins convert to AccountId via the `ParaId::into`.
	SiblingParachainConvertsVia<Sibling, AccountId>,
	// Straight up local `AccountId32` origins just alias directly to `AccountId`.
	AccountId32Aliases<RococoNetwork, AccountId>,
);

/// Means for transacting assets on this chain.
pub type CurrencyTransactor = CurrencyAdapter<
	// Use this currency:
	Balances,
	// Use this currency when it is a fungible asset matching the given location or name:
	IsConcrete<RocLocation>,
	// Do a simple punn to convert an AccountId32 MultiLocation into a native chain account ID:
	LocationToAccountId,
	// Our chain's account ID type (we can't get away without mentioning it explicitly):
	AccountId,
	// We don't track any teleports.
	(),
>;

/// Means for transacting assets besides the native currency on this chain.
pub type FungiblesTransactor = FungiblesAdapter<
	// Use this fungibles implementation:
	Assets,
	// Use this currency when it is a fungible asset matching the given location or name:
	ConvertedConcreteAssetId<
		AssetId,
		u64,
		AsPrefixedGeneralIndex<StatemintLocation, AssetId, JustTry>,
		JustTry,
	>,
	// Convert an XCM MultiLocation into a local account id:
	LocationToAccountId,
	// Our chain's account ID type (we can't get away without mentioning it explicitly):
	AccountId,
	// We only want to allow teleports of known assets. We use non-zero issuance as an indication
	// that this asset is known.
	NonZeroIssuance<AccountId, Assets>,
	// The account to use for tracking teleports.
	CheckingAccount,
>;
/// Means for transacting assets on this chain.
pub type AssetTransactors = (CurrencyTransactor, FungiblesTransactor);

/// This is the type we use to convert an (incoming) XCM origin into a local `Origin` instance,
/// ready for dispatching a transaction with Xcm's `Transact`. There is an `OriginKind` which can
/// biases the kind of local `Origin` it will become.
pub type XcmOriginToTransactDispatchOrigin = (
	// Sovereign account converter; this attempts to derive an `AccountId` from the origin location
	// using `LocationToAccountId` and then turn that into the usual `Signed` origin. Useful for
	// foreign chains who want to have a local sovereign account on this chain which they control.
	SovereignSignedViaLocation<LocationToAccountId, Origin>,
	// Native converter for Relay-chain (Parent) location; will converts to a `Relay` origin when
	// recognised.
	RelayChainAsNative<RelayChainOrigin, Origin>,
	// Native converter for sibling Parachains; will convert to a `SiblingPara` origin when
	// recognised.
	SiblingParachainAsNative<cumulus_pallet_xcm::Origin, Origin>,
	// Superuser converter for the Relay-chain (Parent) location. This will allow it to issue a
	// transaction from the Root origin.
	ParentAsSuperuser<Origin>,
	// Native signed account converter; this just converts an `AccountId32` origin into a normal
	// `Origin::Signed` origin of the same 32-byte value.
	SignedAccountId32AsNative<RococoNetwork, Origin>,
	// Xcm origins can be represented natively under the Xcm pallet's Xcm origin.
	XcmPassthrough<Origin>,
);

parameter_types! {
	// One XCM operation is 1_000_000 weight - almost certainly a conservative estimate.
	pub UnitWeightCost: Weight = 1_000_000;
	// One ROC buys 1 second of weight.
	pub const WeightPrice: (MultiLocation, u128) = (MultiLocation::parent(), IMBU);
	pub const MaxInstructions: u32 = 100;
}

match_type! {
	pub type ParentOrParentsUnitPlurality: impl Contains<MultiLocation> = {
		MultiLocation { parents: 1, interior: Here } |
		MultiLocation { parents: 1, interior: X1(Plurality { id: BodyId::Unit, .. }) }
	};
}
match_type! {
	pub type Statemint: impl Contains<MultiLocation> = {
		MultiLocation { parents: 1, interior: X1(Parachain(1000)) }
	};
}

pub type Barrier = (
	TakeWeightCredit,
	AllowAnyPaidExecutionFrom<Everything>,
	// AllowUnpaidExecutionFrom<IsInVec<AllowUnpaidFrom>>,	// <- Parent gets free execution
);


pub struct AllowAnyPaidExecutionFrom<T>(PhantomData<T>);
impl<T: Contains<MultiLocation>> ShouldExecute for AllowAnyPaidExecutionFrom<T> {
	fn should_execute<Call>(
		origin: &MultiLocation,
		_message: &mut Xcm<Call>,
		_max_weight: Weight,
		_weight_credit: &mut Weight,
	) -> Result<(), ()> {
		ensure!(T::contains(origin), ());
		Ok(())
	}
}
parameter_types! {
	pub StatemintLocation: MultiLocation = MultiLocation::new(1, X1(Parachain(1000)));
}

pub type Reserves = (NativeAsset, AssetsFrom<StatemintLocation>);

pub struct XcmConfig;
impl Config for XcmConfig {
	type Call = Call;
	type XcmSender = XcmRouter;
	// How to withdraw and deposit an asset.
	type AssetTransactor = AssetTransactors;
	type OriginConverter = XcmOriginToTransactDispatchOrigin;
	type IsReserve = Reserves;
	type IsTeleporter = NativeAsset; // <- should be enough to allow teleportation of ROC
	type LocationInverter = LocationInverter<Ancestry>;
	type Barrier = Barrier;
	type Weigher = FixedWeightBounds<UnitWeightCost, Call, MaxInstructions>;
	type Trader = UsingComponents<IdentityFee<Balance>, RocLocation, AccountId, Balances, ()>;
	type ResponseHandler = PolkadotXcm;
	type AssetTrap = PolkadotXcm;
	type AssetClaims = PolkadotXcm;
	type SubscriptionService = PolkadotXcm;
}

parameter_types! {
	pub const MaxDownwardMessageWeight: Weight = MAXIMUM_BLOCK_WEIGHT / 10;
    pub const GracePeriod: u32 = 5;
    pub const UnsignedInterval: u64 = 128;
    pub const UnsignedPriority: u64 = 1 << 20;
}

/// No local origins on this chain are allowed to dispatch XCM sends/executions.
pub type LocalOriginToLocation = SignedToAccountId32<Origin, AccountId, RococoNetwork>;

/// The means for routing XCM messages which are not for local execution into the right message
/// queues.
pub type XcmRouter = (
	// Two routers - use UMP to communicate with the relay chain:
	cumulus_primitives_utility::ParentAsUmp<ParachainSystem, ()>,
	// ..and XCMP to communicate with the sibling chains.
	XcmpQueue,
);

impl pallet_xcm::Config for Runtime {
	type Event = Event;
	type SendXcmOrigin = EnsureXcmOrigin<Origin, LocalOriginToLocation>;
	type XcmRouter = XcmRouter;
	type ExecuteXcmOrigin = EnsureXcmOrigin<Origin, LocalOriginToLocation>;
	type XcmExecuteFilter = Everything;
	type XcmExecutor = XcmExecutor<XcmConfig>;
	type XcmTeleportFilter = Everything;
	type XcmReserveTransferFilter = frame_support::traits::Nothing;
	type Weigher = FixedWeightBounds<UnitWeightCost, Call, MaxInstructions>;
	type LocationInverter = LocationInverter<Ancestry>;
	type Origin = Origin;
	type Call = Call;
	const VERSION_DISCOVERY_QUEUE_SIZE: u32 = 100;
	type AdvertisedXcmVersion = pallet_xcm::CurrentXcmVersion;
}

impl cumulus_pallet_xcm::Config for Runtime {
	type Event = Event;
	type XcmExecutor = XcmExecutor<XcmConfig>;
}

impl cumulus_pallet_xcmp_queue::Config for Runtime {
	type Event = Event;
	type XcmExecutor = XcmExecutor<XcmConfig>;
	type ChannelInfo = ParachainSystem;
	type VersionWrapper = ();
}

impl cumulus_pallet_dmp_queue::Config for Runtime {
	type Event = Event;
	type XcmExecutor = XcmExecutor<XcmConfig>;
	type ExecuteOverweightOrigin = frame_system::EnsureRoot<AccountId>;
}


parameter_types! {
	pub const MinVestedTransfer: Balance = MIN_VESTING * IMBU;
}

impl pallet_vesting::Config for Runtime {
	type Event = Event;
	type Currency = Balances;
	type BlockNumberToBalance = ConvertInto;
	type MinVestedTransfer = MinVestedTransfer;
	type WeightInfo = pallet_vesting::weights::SubstrateWeight<Self>;
	const MAX_VESTING_SCHEDULES: u32 = 28;
}

parameter_types! {
	pub const MinimumReward: Balance = 0;
	pub const Initialized: bool = false;
	pub const InitializationPayment: Perbill = Perbill::from_percent(30);
	pub const MaxInitContributorsBatchSizes: u32 = 500;
	pub const RelaySignaturesThreshold: Perbill = Perbill::from_percent(100);
}

impl pallet_utility::Config for Runtime {
	type Event = Event;
	type Call = Call;
	type WeightInfo = pallet_utility::weights::SubstrateWeight<Runtime>;
}


parameter_types! {
	pub MaximumSchedulerWeight: Weight = NORMAL_DISPATCH_RATIO * RuntimeBlockWeights::get().max_block;
	pub const MaxScheduledPerBlock: u32 = 50;
}

impl pallet_scheduler::Config for Runtime {
	type Event = Event;
	type Origin = Origin;
	type PalletsOrigin = OriginCaller;
	type Call = Call;
	type MaximumWeight = MaximumSchedulerWeight;
	type ScheduleOrigin = EnsureRoot<AccountId>;
	type MaxScheduledPerBlock = MaxScheduledPerBlock;
	type WeightInfo = weights::pallet_scheduler::WeightInfo<Runtime>;
}


parameter_types! {
	pub const StakingUnsignedPriority: TransactionPriority = TransactionPriority::max_value() / 2;
}


impl<LocalCall> frame_system::offchain::CreateSignedTransaction<LocalCall> for Runtime where
	Call: From<LocalCall>,
{
	fn create_transaction<C: frame_system::offchain::AppCrypto<Self::Public, Self::Signature>>(
		call: Call,
		public: <Signature as Verify>::Signer,
		account: AccountId,
		nonce: <Runtime as frame_system::Config>::Index,
	) -> Option<(Call, <UncheckedExtrinsic as ExtrinsicT>::SignaturePayload)> {
		use sp_runtime::traits::StaticLookup;
		// take the biggest period possible.
		let period = BlockHashCount::get()
			.checked_next_power_of_two()
			.map(|c| c / 2)
			.unwrap_or(2) as u64;

		let current_block = System::block_number()
			// The `System::block_number` is initialized with `n+1`,
			// so the actual block number is `n`.
			.saturating_sub(1).into();
		let tip = 0;
		let era = Era::mortal(period, current_block);
		let extra = (
			frame_system::CheckSpecVersion::<Runtime>::new(),
			frame_system::CheckGenesis::<Runtime>::new(),
			frame_system::CheckEra::<Runtime>::from(era),
			frame_system::CheckNonce::<Runtime>::from(nonce),
			frame_system::CheckWeight::<Runtime>::new(),
			pallet_transaction_payment::ChargeTransactionPayment::<Runtime>::from(tip),
		);
		let raw_payload = SignedPayload::new(call, extra)
			.map_err(|e| {
				log::warn!("Unable to create signed payload: {:?}", e);
			})
			.ok()?;

		let signature = raw_payload.using_encoded(|payload| C::sign(payload, public))?;
		let (call, extra, _) = raw_payload.deconstruct();
		let address = <Runtime as frame_system::Config>::Lookup::unlookup(account);
		Some((call, (address, signature, extra)))
	}
}


impl frame_system::offchain::SigningTypes for Runtime {
	type Public = <Signature as sp_runtime::traits::Verify>::Signer;
	type Signature = Signature;
}

impl<C> frame_system::offchain::SendTransactionTypes<C> for Runtime
	where
		Call: From<C>,
{
	type OverarchingCall = Call;
	type Extrinsic = UncheckedExtrinsic;
}

parameter_types! {
	pub const AssetDeposit: Balance = 1 * IMBU;
	pub const ApprovalDeposit: Balance = 100 * MILLI_IMBU;
	pub const AssetsStringLimit: u32 = 50;
	pub const MetadataDepositBase: Balance = 1 * IMBU;
	pub const MetadataDepositPerByte: Balance = 10 * MILLI_IMBU;
	pub const UnitBody: BodyId = BodyId::Unit;
}

/// A majority of the Unit body from Rococo over XCM is our required administration origin.
pub type AdminOrigin = EnsureOneOf<
	AccountId,
	EnsureRoot<AccountId>,
	EnsureXcm<IsMajorityOfBody<RocLocation, UnitBody>>,
>;

impl pallet_assets::Config for Runtime {
	type Event = Event;
	type Balance = u64;
	type AssetId = AssetId;
	type Currency = Balances;
	type ForceOrigin = AdminOrigin;
	type AssetDeposit = AssetDeposit;
	type MetadataDepositBase = MetadataDepositBase;
	type MetadataDepositPerByte = MetadataDepositPerByte;
	type ApprovalDeposit = ApprovalDeposit;
	type StringLimit = AssetsStringLimit;
	type Freezer = ();
	type Extra = ();
	type WeightInfo = pallet_assets::weights::SubstrateWeight<Runtime>;
}

impl pallet_aura::Config for Runtime {
	type AuthorityId = AuraId;
	type DisabledValidators = ();
	type MaxAuthorities = MaxAuthorities;
}


parameter_types! {
	pub const PotId: PalletId = PalletId(*b"PotStake");
	pub const MaxCandidates: u32 = 1000;
	pub const MinCandidates: u32 = 5;
	pub const SessionLength: BlockNumber = 6 * HOURS;
	pub const MaxInvulnerables: u32 = 100;
	pub const ExecutiveBody: BodyId = BodyId::Executive;
}

// We allow root only to execute privileged collator selection operations.
pub type CollatorSelectionUpdateOrigin = EnsureRoot<AccountId>;

impl pallet_collator_selection::Config for Runtime {
	type Event = Event;
	type Currency = Balances;
	type UpdateOrigin = CollatorSelectionUpdateOrigin;
	type PotId = PotId;
	type MaxCandidates = MaxCandidates;
	type MinCandidates = MinCandidates;
	type MaxInvulnerables = MaxInvulnerables;
	// should be a multiple of session or things will get inconsistent
	type KickThreshold = Period;
	type ValidatorId = <Self as frame_system::Config>::AccountId;
	type ValidatorIdOf = pallet_collator_selection::IdentityCollator;
	type ValidatorRegistration = Session;
	type WeightInfo = ();
}

parameter_types! {
	pub const BasicDeposit: Balance = 10 * IMBU;       // 258 bytes on-chain
	pub const FieldDeposit: Balance = 250 * CENTI_IMBU;        // 66 bytes on-chain
	pub const SubAccountDeposit: Balance = 2 * IMBU;   // 53 bytes on-chain
	pub const MaxSubAccounts: u32 = 100;
	pub const MaxAdditionalFields: u32 = 100;
	pub const MaxRegistrars: u32 = 20;
}

impl pallet_identity::Config for Runtime {
	type Event = Event;
	type Currency = Balances;
	type BasicDeposit = BasicDeposit;
	type FieldDeposit = FieldDeposit;
	type SubAccountDeposit = SubAccountDeposit;
	type MaxSubAccounts = MaxSubAccounts;
	type MaxAdditionalFields = MaxAdditionalFields;
	type MaxRegistrars = MaxRegistrars;
	type Slashed = Treasury;
	type ForceOrigin = MoreThanHalfCouncil;
	type RegistrarOrigin = MoreThanHalfCouncil;
	type WeightInfo = weights::pallet_identity::WeightInfo<Runtime>;
}

parameter_types! {
	pub const UncleGenerations: BlockNumber = 5;
}

impl pallet_authorship::Config for Runtime {
	type FindAuthor = pallet_session::FindAccountFromAuthorIndex<Self, Aura>;
	type UncleGenerations = UncleGenerations;
	type FilterUncle = ();
	type EventHandler = (CollatorSelection,);
}

parameter_types! {
	pub const TechnicalMotionDuration: BlockNumber = 5 * DAYS;
	pub const TechnicalMaxProposals: u32 = 100;
	pub const TechnicalMaxMembers: u32 = 100;
}

type TechnicalCollective = pallet_collective::Instance2;
impl pallet_collective::Config<TechnicalCollective> for Runtime {
	type Origin = Origin;
	type Proposal = Call;
	type Event = Event;
	type MotionDuration = TechnicalMotionDuration;
	type MaxProposals = TechnicalMaxProposals;
	type MaxMembers = TechnicalMaxMembers;
	type DefaultVote = pallet_collective::PrimeDefaultVote;
	type WeightInfo = pallet_collective::weights::SubstrateWeight<Runtime>;
}
parameter_types! {
	pub const Period: u32 = 6 * HOURS;
	pub const Offset: u32 = 0;
	pub const MaxAuthorities: u32 = 100_000;
}

impl pallet_session::Config for Runtime {
	type Event = Event;
	type ValidatorId = <Self as frame_system::Config>::AccountId;
	// we don't have stash and controller, thus we don't need the convert as well.
	type ValidatorIdOf = pallet_collator_selection::IdentityCollator;
	type ShouldEndSession = pallet_session::PeriodicSessions<Period, Offset>;
	type NextSessionRotation = pallet_session::PeriodicSessions<Period, Offset>;
	type SessionManager = CollatorSelection;
	// Essentially just Aura, but lets be pedantic.
	type SessionHandler = <SessionKeys as sp_runtime::traits::OpaqueKeys>::KeyTypeIdProviders;
	type Keys = SessionKeys;
	type WeightInfo = ();
}

// impl pallet_session::historical::Config for Runtime {
// 	type FullIdentification = pallet_staking::Exposure<AccountId, Balance>;
// 	type FullIdentificationOf = pallet_staking::ExposureOf<Runtime>;
// }

// pallet_staking_reward_curve::build! {
// 	const REWARD_CURVE: PiecewiseLinear<'static> = curve!(
// 		min_inflation: 0_025_000,
// 		max_inflation: 0_100_000,
// 		ideal_stake: 0_500_000,
// 		falloff: 0_050_000,
// 		max_piece_count: 40,
// 		test_precision: 0_005_000,
// 	);
// }

parameter_types! {
	// phase durations. 1/4 of the last session for each.
	pub const SignedPhase: u32 = EPOCH_DURATION_IN_SLOTS / 4;
	pub const UnsignedPhase: u32 = EPOCH_DURATION_IN_SLOTS / 4;

	// signed config
	pub const SignedMaxSubmissions: u32 = 16;
	pub const SignedDepositBase: Balance = deposit(2, 0);
	pub const SignedDepositByte: Balance = deposit(0, 10) / 1024;
	// Each good submission will get 1/10 KSM as reward
	pub SignedRewardBase: Balance =  IMBU / 10;
	pub SolutionImprovementThreshold: Perbill = Perbill::from_rational(5u32, 10_000);

	// 1 hour session, 15 minutes unsigned phase, 8 offchain executions.
	pub OffchainRepeat: BlockNumber = UnsignedPhase::get() / 8;

	/// Whilst `UseNominatorsAndUpdateBagsList` or `UseNominatorsMap` is in use, this can still be a
	/// very large value. Once the `BagsList` is in full motion, staking might open its door to many
	/// more nominators, and this value should instead be what is a "safe" number (e.g. 22500).
	pub const VoterSnapshotPerBlock: u32 = 22_500;
}

// sp_npos_elections::generate_solution_type!(
// 	#[compact]
// 	pub struct NposCompactSolution24::<
// 		VoterIndex = u32,
// 		TargetIndex = u16,
// 		Accuracy = sp_runtime::PerU16,
// 	>(24)
// );

// impl pallet_election_provider_multi_phase::Config for Runtime {
// 	type Event = Event;
// 	type Currency = Balances;
// 	type EstimateCallFee = TransactionPayment;
// 	type UnsignedPhase = UnsignedPhase;
// 	type SignedMaxSubmissions = SignedMaxSubmissions;
// 	type SignedRewardBase = SignedRewardBase;
// 	type SignedDepositBase = SignedDepositBase;
// 	type SignedDepositByte = SignedDepositByte;
// 	type SignedDepositWeight = ();
// 	type SignedMaxWeight = Self::MinerMaxWeight;
// 	type SlashHandler = (); // burn slashes
// 	type RewardHandler = (); // nothing to do upon rewards
// 	type SignedPhase = SignedPhase;
// 	type SolutionImprovementThreshold = SolutionImprovementThreshold;
// 	type MinerMaxWeight = OffchainSolutionWeightLimit; // For now use the one from staking.
// 	type MinerMaxLength = OffchainSolutionLengthLimit;
// 	type OffchainRepeat = OffchainRepeat;
// 	type MinerTxPriority = NposSolutionPriority;
// 	type DataProvider = Staking;
// 	type Solution = NposCompactSolution24;
// 	type Fallback = pallet_election_provider_multi_phase::NoFallback<Self>;
// 	type Solver = frame_election_provider_support::SequentialPhragmen<
// 		AccountId,
// 		pallet_election_provider_multi_phase::SolutionAccuracyOf<Self>,
// 		runtime_common::elections::OffchainRandomBalancing,
// 	>;
// 	type BenchmarkingConfig = runtime_common::elections::BenchmarkConfig;
// 	type ForceOrigin = EnsureOneOf<
// 		AccountId,
// 		EnsureRoot<AccountId>,
// 		pallet_collective::EnsureProportionAtLeast<_2, _3, AccountId, CouncilCollective>,
// 	>;
// 	type WeightInfo = weights::pallet_election_provider_multi_phase::WeightInfo<Self>;
// 	type VoterSnapshotPerBlock = VoterSnapshotPerBlock;
// }

// const MAX_NOMINATIONS: u32 = <NposCompactSolution24 as sp_npos_elections::NposSolution>::LIMIT as u32;

parameter_types! {
	/// A limit for off-chain phragmen unsigned solution submission.
	///
	/// We want to keep it as high as possible, but can't risk having it reject,
	/// so we always subtract the base block execution weight.
	pub OffchainSolutionWeightLimit: Weight = BlockWeights::get()
		.get(DispatchClass::Normal)
		.max_extrinsic
		.expect("Normal extrinsics have weight limit configured by default; qed")
		.saturating_sub(BlockExecutionWeight::get());

	/// A limit for off-chain phragmen unsigned solution length.
	///
	/// We allow up to 90% of the block's size to be consumed by the solution.
	pub OffchainSolutionLengthLimit: u32 = Perbill::from_rational(90_u32, 100) *
		*BlockLength::get()
		.max
		.get(DispatchClass::Normal);
}

/// The numbers configured here should always be more than the the maximum limits of staking pallet
/// to ensure election snapshot will not run out of memory.
// pub struct BenchmarkConfig;
// impl pallet_election_provider_multi_phase::BenchmarkingConfig for BenchmarkConfig {
// 	const VOTERS: [u32; 2] = [5_000, 10_000];
// 	const TARGETS: [u32; 2] = [1_000, 2_000];
// 	const ACTIVE_VOTERS: [u32; 2] = [1000, 4_000];
// 	const DESIRED_TARGETS: [u32; 2] = [400, 800];
// 	const SNAPSHOT_MAXIMUM_VOTERS: u32 = 25_000;
// 	const MINER_MAXIMUM_VOTERS: u32 = 15_000;
// 	const MAXIMUM_TARGETS: u32 = 2000;
// }


fn era_payout(
	total_staked: Balance,
	non_gilt_issuance: Balance,
	max_annual_inflation: Perquintill,
	period_fraction: Perquintill,
	auctioned_slots: u64,
) -> (Balance, Balance) {
	use pallet_staking_reward_fn::compute_inflation;
	use sp_arithmetic::traits::Saturating;

	let min_annual_inflation = Perquintill::from_rational(25u64, 1000u64);
	let delta_annual_inflation = max_annual_inflation.saturating_sub(min_annual_inflation);

	// 30% reserved for up to 60 slots.
	let auction_proportion = Perquintill::from_rational(auctioned_slots.min(60), 200u64);

	// Therefore the ideal amount at stake (as a percentage of total issuance) is 75% less the amount that we expect
	// to be taken up with auctions.
	let ideal_stake = Perquintill::from_percent(75).saturating_sub(auction_proportion);

	let stake = Perquintill::from_rational(total_staked, non_gilt_issuance);
	let falloff = Perquintill::from_percent(5);
	let adjustment = compute_inflation(stake, ideal_stake, falloff);
	let staking_inflation =
		min_annual_inflation.saturating_add(delta_annual_inflation * adjustment);

	let max_payout = period_fraction * max_annual_inflation * non_gilt_issuance;
	let staking_payout = (period_fraction * staking_inflation) * non_gilt_issuance;
	let rest = max_payout.saturating_sub(staking_payout);

	let other_issuance = non_gilt_issuance.saturating_sub(total_staked);
	if total_staked > other_issuance {
		let _cap_rest = Perquintill::from_rational(other_issuance, total_staked) * staking_payout;
		// We don't do anything with this, but if we wanted to, we could introduce a cap on the treasury amount
		// with: `rest = rest.min(cap_rest);`
	}
	(staking_payout, rest)
}

// pub struct EraPayout;
// impl pallet_staking::EraPayout<Balance> for EraPayout {
// 	fn era_payout(
// 		total_staked: Balance,
// 		_total_issuance: Balance,
// 		era_duration_millis: u64,
// 	) -> (Balance, Balance) {
// 		// TODO: #3011 Update with proper auctioned slots tracking.
// 		// This should be fine for the first year of parachains.
// 		let auctioned_slots: u64 = auctions::Pallet::<Runtime>::auction_counter().into();
// 		const MAX_ANNUAL_INFLATION: Perquintill = Perquintill::from_percent(10);
// 		const MILLISECONDS_PER_YEAR: u64 = 1000 * 3600 * 24 * 36525 / 100;

// 		era_payout(
// 			total_staked,
// 			Gilt::issuance().non_gilt,
// 			MAX_ANNUAL_INFLATION,
// 			Perquintill::from_rational(era_duration_millis, MILLISECONDS_PER_YEAR),
// 			auctioned_slots,
// 		)
// 	}
// }


parameter_types! {
	// Six sessions in an era (6 hours).
	pub const SessionsPerEra: SessionIndex = 6;
	// 28 eras for unbonding (7 days).
	pub const BondingDuration: pallet_staking::EraIndex = 28;
	// 27 eras in which slashes can be cancelled (slightly less than 7 days).
	pub const SlashDeferDuration: pallet_staking::EraIndex = 27;
	pub const MaxNominatorRewardedPerValidator: u32 = 256;
	pub const OffendingValidatorsThreshold: Perbill = Perbill::from_percent(17);
}

type SlashCancelOrigin = EnsureOneOf<
	AccountId,
	EnsureRoot<AccountId>,
	pallet_collective::EnsureProportionAtLeast<_1, _2, AccountId, CouncilCollective>,
>;

// impl frame_election_provider_support::onchain::Config for Runtime {
// 	type Accuracy = runtime_common::elections::OnOnChainAccuracy;
// 	type DataProvider = Staking;
// }

// impl pallet_staking::Config for Runtime {
// 	const MAX_NOMINATIONS: u32 =
// 		<NposCompactSolution24 as sp_npos_elections::NposSolution>::LIMIT as u32;
// 	type Currency = Balances;
// 	type UnixTime = Timestamp;
// 	type CurrencyToVote = CurrencyToVote;
// 	type ElectionProvider = ElectionProviderMultiPhase;
// 	type GenesisElectionProvider = runtime_common::elections::GenesisElectionOf<Self>;
// 	type RewardRemainder = Treasury;
// 	type Event = Event;
// 	type Slash = Treasury;
// 	type Reward = ();
// 	type SessionsPerEra = SessionsPerEra;
// 	type BondingDuration = BondingDuration;
// 	type SlashDeferDuration = SlashDeferDuration;
// 	// A majority of the council or root can cancel the slash.
// 	type SlashCancelOrigin = SlashCancelOrigin;
// 	type SessionInterface = Self;
// 	type EraPayout = EraPayout;
// 	type NextNewSession = Session;
// 	type MaxNominatorRewardedPerValidator = MaxNominatorRewardedPerValidator;
// 	type OffendingValidatorsThreshold = OffendingValidatorsThreshold;
// 	// Use the nominators map to iter voters, but also perform the bags-list migration and keep
// 	// it up-to-date.
// 	type SortedListProvider = runtime_common::elections::UseNominatorsAndUpdateBagsList<Runtime>;
// 	type WeightInfo = weights::pallet_staking::WeightInfo<Runtime>;
// }


parameter_types! {
	pub const EpochDuration: u64 = EPOCH_DURATION_IN_SLOTS as u64;
	pub const ExpectedBlockTime: Moment = MILLISECS_PER_BLOCK;
	pub const ReportLongevity: u64 =
		BondingDuration::get() as u64 * SessionsPerEra::get() as u64 * EpochDuration::get();
}

// impl pallet_babe::Config for Runtime {
// 	type EpochDuration = EpochDuration;
// 	type ExpectedBlockTime = ExpectedBlockTime;

// 	// session module is the trigger
// 	type EpochChangeTrigger = pallet_babe::ExternalTrigger;

// 	type DisabledValidators = Session;

// 	type KeyOwnerProof = <Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(
// 		KeyTypeId,
// 		pallet_babe::AuthorityId,
// 	)>>::Proof;

// 	type KeyOwnerIdentification = <Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(
// 		KeyTypeId,
// 		pallet_babe::AuthorityId,
// 	)>>::IdentificationTuple;

// 	type KeyOwnerProofSystem = Historical;

// 	type HandleEquivocation =
// 		pallet_babe::EquivocationHandler<Self::KeyOwnerIdentification, Offences, ReportLongevity>;

// 	type WeightInfo = ();

// 	type MaxAuthorities = MaxAuthorities;
// }

// impl pallet_offences::Config for Runtime {
// 	type Event = Event;
// 	type IdentificationTuple = pallet_session::historical::IdentificationTuple<Self>;
// 	type OnOffenceHandler = Staking;
// }





impl pallet_membership::Config<pallet_membership::Instance1> for Runtime {
	type Event = Event;
	type AddOrigin = MoreThanHalfCouncil;
	type RemoveOrigin = MoreThanHalfCouncil;
	type SwapOrigin = MoreThanHalfCouncil;
	type ResetOrigin = MoreThanHalfCouncil;
	type PrimeOrigin = MoreThanHalfCouncil;
	type MembershipInitialized = TechnicalCommittee;
	type MembershipChanged = TechnicalCommittee;
	type MaxMembers = TechnicalMaxMembers;
	type WeightInfo = weights::pallet_membership::WeightInfo<Runtime>;
}

parameter_types! {
	pub const CouncilMotionDuration: BlockNumber = 5 * DAYS;
	pub const CouncilMaxProposals: u32 = 100;
	pub const CouncilMaxMembers: u32 = 100;
}

type CouncilCollective = pallet_collective::Instance1;
impl pallet_collective::Config<CouncilCollective> for Runtime {
	type Origin = Origin;
	type Proposal = Call;
	type Event = Event;
	type MotionDuration = CouncilMotionDuration;
	type MaxProposals = CouncilMaxProposals;
	type MaxMembers = CouncilMaxMembers;
	type DefaultVote = pallet_collective::PrimeDefaultVote;
	type WeightInfo = weights::pallet_collective_council::WeightInfo<Runtime>;
}

parameter_types! {
	pub const ProposalBond: Permill = Permill::from_percent(5);
	pub const ProposalBondMinimum: Balance = 2000 * CENTI_IMBU;
	pub const SpendPeriod: BlockNumber = 6 * DAYS;
	pub const Burn: Permill = Permill::from_perthousand(2);
	pub const TreasuryPalletId: PalletId = PalletId(*b"py/trsry");

	pub const TipCountdown: BlockNumber = 1 * DAYS;
	pub const TipFindersFee: Percent = Percent::from_percent(20);
	pub const TipReportDepositBase: Balance = 100 * CENTI_IMBU;
	pub const DataDepositPerByte: Balance = 1 * CENTI_IMBU;
	pub const BountyDepositBase: Balance = 100 * CENTI_IMBU;
	pub const BountyDepositPayoutDelay: BlockNumber = 4 * DAYS;
	pub const BountyUpdatePeriod: BlockNumber = 90 * DAYS;
	pub const MaximumReasonLength: u32 = 16384;
	pub const BountyCuratorDeposit: Permill = Permill::from_percent(50);
	pub const BountyValueMinimum: Balance = 200 * CENTI_IMBU;
	pub const MaxApprovals: u32 = 100;
	pub const MaxKeys: u32 = 10_000;
	pub const MaxPeerInHeartbeats: u32 = 10_000;
	pub const MaxPeerDataEncodingSize: u32 = 1_000;
}

impl pallet_treasury::Config for Runtime {
	type PalletId = TreasuryPalletId;
	type Currency = Balances;
	type ApproveOrigin = EnsureOneOf<
		AccountId,
		EnsureRoot<AccountId>,
		pallet_collective::EnsureProportionAtLeast<_3, _5, AccountId, CouncilCollective>,
	>;
	type RejectOrigin = EnsureOneOf<
		AccountId,
		EnsureRoot<AccountId>,
		pallet_collective::EnsureProportionMoreThan<_1, _2, AccountId, CouncilCollective>,
	>;
	type Event = Event;
	type OnSlash = ();
	type ProposalBond = ProposalBond;
	type ProposalBondMinimum = ProposalBondMinimum;
	type SpendPeriod = SpendPeriod;
	type Burn = Burn;
	type BurnDestination = ();
	type SpendFunds = Bounties;
	type WeightInfo = pallet_treasury::weights::SubstrateWeight<Runtime>;
	type MaxApprovals = MaxApprovals;
}

impl pallet_bounties::Config for Runtime {
	type BountyDepositBase = BountyDepositBase;
	type BountyDepositPayoutDelay = BountyDepositPayoutDelay;
	type BountyUpdatePeriod = BountyUpdatePeriod;
	type BountyCuratorDeposit = BountyCuratorDeposit;
	type BountyValueMinimum = BountyValueMinimum;
	type DataDepositPerByte = DataDepositPerByte;
	type Event = Event;
	type MaximumReasonLength = MaximumReasonLength;
	type WeightInfo = weights::pallet_bounties::WeightInfo<Runtime>;
}

// parameter_types! {
// 	pub NposSolutionPriority: TransactionPriority =
// 		Perbill::from_percent(90) * TransactionPriority::max_value();
// 	pub const ImOnlineUnsignedPriority: TransactionPriority = TransactionPriority::max_value();
// }

// impl pallet_im_online::Config for Runtime {
// 	type AuthorityId = ImOnlineId;
// 	type Event = Event;
// 	type NextSessionRotation = Babe;
// 	type ValidatorSet = Historical;
// 	type ReportUnresponsiveness = Offences;
// 	type UnsignedPriority = ImOnlineUnsignedPriority;
// 	type WeightInfo = pallet_im_online::weights::SubstrateWeight<Runtime>;
// }

// Configure the pallet quadratic funding in pallets/quadratic-funding.
parameter_types! {
	pub const GrantsPalletId: PalletId = PalletId(*b"imbgrant");
	pub const MaxGrantsPerRound: u32 = 256;
	pub const MaxWithdrawalExpiration: BlockNumber = 180 * DAYS;
}

impl grants::Config for Runtime {
	type Event = Event;
	type PalletId = GrantsPalletId;
	type Currency = Balances;
	type MaxGrantsPerRound = MaxGrantsPerRound;
	type MaxWithdrawalExpiration = MaxWithdrawalExpiration;
	type WeightInfo = ();
}


construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = opaque::Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Storage, Config, Event<T>},
		Timestamp: pallet_timestamp::{Pallet, Call, Storage, Inherent},
		Sudo: pallet_sudo::{Pallet, Call, Storage, Config<T>, Event<T>},
		RandomnessCollectiveFlip: pallet_randomness_collective_flip::{Pallet, Storage},
		TransactionPayment: pallet_transaction_payment::{Pallet, Storage},
		// Babe: pallet_babe::{Pallet, Call, Storage, Config, ValidateUnsigned},
		// Grandpa: pallet_grandpa::{Pallet, Call, Storage, Config, Event, ValidateUnsigned},
		// Offences: pallet_offences::{Pallet, Storage, Event},
		// Historical: session_historical::{Pallet},
		// Staking: pallet_staking::{Pallet, Call, Config<T>, Storage, Event<T>},
		Session: pallet_session::{Pallet, Call, Storage, Event, Config<T>},
		// ElectionProviderMultiPhase: pallet_election_provider_multi_phase::{Pallet, Call, Storage, Event<T>, ValidateUnsigned},
		TechnicalMembership: pallet_membership::<Instance1>::{Pallet, Call, Storage, Event<T>, Config<T>},
		// Gilt: pallet_gilt::{Pallet, Call, Storage, Event<T>, Config},
		// ImOnline: pallet_im_online::{Pallet, Call, Storage, Event<T>, ValidateUnsigned, Config<T>},



		ParachainSystem: cumulus_pallet_parachain_system::{Pallet, Call, Config, Storage, Inherent, Event<T>, ValidateUnsigned,},
		ParachainInfo: parachain_info::{Pallet, Storage, Config},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Assets: pallet_assets::{Pallet, Call, Storage, Event<T>},
		Vesting: pallet_vesting::{Pallet, Call, Storage, Event<T>, Config<T>},
		Scheduler: pallet_scheduler::{Pallet, Storage, Config, Event<T>, Call},
		Treasury: pallet_treasury::{Pallet, Call, Storage, Config, Event<T>},
		TechnicalCommittee: pallet_collective::<Instance2>::{Pallet, Call, Storage, Origin<T>, Event<T>, Config<T>},
		Bounties: pallet_bounties::{Pallet, Call, Storage, Event<T>},

		Utility: pallet_utility::{Pallet, Call, Event},
		Identity: pallet_identity::{Pallet, Call, Storage, Event<T>},


		Aura: pallet_aura::{Pallet, Config<T>},
		AuraExt: cumulus_pallet_aura_ext::{Pallet, Config},
		Authorship: pallet_authorship::{Pallet, Call, Storage, Inherent},
		CollatorSelection: pallet_collator_selection::{Pallet, Call, Storage, Event<T>, Config<T>},




		// XCM helpers.
		XcmpQueue: cumulus_pallet_xcmp_queue::{Pallet, Call, Storage, Event<T>},
		PolkadotXcm: pallet_xcm::{Pallet, Call, Event<T>, Origin},
		CumulusXcm: cumulus_pallet_xcm::{Pallet, Call, Event<T>, Origin},
		DmpQueue: cumulus_pallet_dmp_queue::{Pallet, Call, Storage, Event<T>},

		// Imbue Pallets
		ImbueGrantsPallet: grants::{Pallet, Call, Storage, Event<T>},
	}
}

pub type Block = generic::Block<Header, UncheckedExtrinsic>;
/// A Block signed with a Justification
pub type SignedBlock = generic::SignedBlock<Block>;
/// BlockId type as expected by this runtime.
pub type BlockId = generic::BlockId<Block>;
/// The SignedExtension to the basic transaction logic.
pub type SignedExtra = (
	frame_system::CheckSpecVersion<Runtime>,
	frame_system::CheckGenesis<Runtime>,
	frame_system::CheckEra<Runtime>,
	frame_system::CheckNonce<Runtime>,
	frame_system::CheckWeight<Runtime>,
	pallet_transaction_payment::ChargeTransactionPayment<Runtime>,
);
/// Unchecked extrinsic type as expected by this runtime.
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<Address, Call, Signature, SignedExtra>;
/// Extrinsic type that has already been checked.
pub type CheckedExtrinsic = generic::CheckedExtrinsic<AccountId, Call, SignedExtra>;
/// Executive: handles dispatch to the various modules.
pub type Executive = frame_executive::Executive<
	Runtime,
	Block,
	frame_system::ChainContext<Runtime>,
	Runtime,
	AllPallets,
>;

impl_runtime_apis! {
	impl sp_api::Core<Block> for Runtime {
		fn version() -> RuntimeVersion {
			VERSION
		}

		fn execute_block(block: Block) {
			Executive::execute_block(block);
		}

		fn initialize_block(header: &<Block as BlockT>::Header) {
			Executive::initialize_block(header)
		}
	}

	impl sp_api::Metadata<Block> for Runtime {
		fn metadata() -> OpaqueMetadata {
			OpaqueMetadata::new(Runtime::metadata().into())
		}
	}

	impl sp_block_builder::BlockBuilder<Block> for Runtime {
		fn apply_extrinsic(
			extrinsic: <Block as BlockT>::Extrinsic,
		) -> ApplyExtrinsicResult {
			Executive::apply_extrinsic(extrinsic)
		}

		fn finalize_block() -> <Block as BlockT>::Header {
			Executive::finalize_block()
		}

		fn inherent_extrinsics(data: sp_inherents::InherentData) -> Vec<<Block as BlockT>::Extrinsic> {
			data.create_extrinsics()
		}

		fn check_inherents(block: Block, data: sp_inherents::InherentData) -> sp_inherents::CheckInherentsResult {
			data.check_extrinsics(&block)
		}
	}

	impl sp_transaction_pool::runtime_api::TaggedTransactionQueue<Block> for Runtime {
		fn validate_transaction(
			source: TransactionSource,
			tx: <Block as BlockT>::Extrinsic,
			block_hash: <Block as BlockT>::Hash,
		) -> TransactionValidity {
			Executive::validate_transaction(source, tx, block_hash)
		}
	}

	impl sp_offchain::OffchainWorkerApi<Block> for Runtime {
		fn offchain_worker(header: &<Block as BlockT>::Header) {
			Executive::offchain_worker(header)
		}
	}

	impl sp_session::SessionKeys<Block> for Runtime {
		fn decode_session_keys(
			encoded: Vec<u8>,
		) -> Option<Vec<(Vec<u8>, sp_core::crypto::KeyTypeId)>> {
			SessionKeys::decode_into_raw_public_keys(&encoded)
		}

		fn generate_session_keys(seed: Option<Vec<u8>>) -> Vec<u8> {
			SessionKeys::generate(seed)
		}
	}

	impl sp_consensus_aura::AuraApi<Block, AuraId> for Runtime {
		fn slot_duration() -> sp_consensus_aura::SlotDuration {
			sp_consensus_aura::SlotDuration::from_millis(Aura::slot_duration())
		}

		fn authorities() -> Vec<AuraId> {
			Aura::authorities().into_inner()
		}
	}

	impl frame_system_rpc_runtime_api::AccountNonceApi<Block, AccountId, Index> for Runtime {
		fn account_nonce(account: AccountId) -> Index {
			System::account_nonce(account)
		}
	}

	impl pallet_transaction_payment_rpc_runtime_api::TransactionPaymentApi<Block, Balance> for Runtime {
		fn query_info(
			uxt: <Block as BlockT>::Extrinsic,
			len: u32,
		) -> pallet_transaction_payment_rpc_runtime_api::RuntimeDispatchInfo<Balance> {
			TransactionPayment::query_info(uxt, len)
		}
		fn query_fee_details(
			uxt: <Block as BlockT>::Extrinsic,
			len: u32,
		) -> pallet_transaction_payment::FeeDetails<Balance> {
			TransactionPayment::query_fee_details(uxt, len)
		}
	}

	impl cumulus_primitives_core::CollectCollationInfo<Block> for Runtime {
		fn collect_collation_info() -> cumulus_primitives_core::CollationInfo {
			ParachainSystem::collect_collation_info()
		}
	}
}

struct CheckInherents;

impl cumulus_pallet_parachain_system::CheckInherents<Block> for CheckInherents {
	fn check_inherents(
		block: &Block,
		relay_state_proof: &cumulus_pallet_parachain_system::RelayChainStateProof,
	) -> sp_inherents::CheckInherentsResult {
		let relay_chain_slot = relay_state_proof
			.read_slot()
			.expect("Could not read the relay chain slot from the proof");

		let inherent_data =
			cumulus_primitives_timestamp::InherentDataProvider::from_relay_chain_slot_and_duration(
				relay_chain_slot,
				sp_std::time::Duration::from_secs(6),
			)
				.create_inherent_data()
				.expect("Could not create the timestamp inherent data");

		inherent_data.check_extrinsics(&block)
	}
}

cumulus_pallet_parachain_system::register_validate_block! {
	Runtime = Runtime,
	BlockExecutor = cumulus_pallet_aura_ext::BlockExecutor::<Runtime, Executive>,
	CheckInherents = CheckInherents,
}
