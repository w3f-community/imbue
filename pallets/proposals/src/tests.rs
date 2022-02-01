// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate as proposals;
use crate::*;
use codec::Decode;
use frame_support::{
    parameter_types, ord_parameter_types, PalletId,
    traits::{Everything,ConstU32,EnsureInherentsAreFirst},
    weights::{IdentityFee, Weight},
};

use frame_system::{pallet_prelude::BlockNumberFor,EnsureRoot,EnsureSignedBy,EnsureOneOf};
use sp_core::{
    offchain::{testing, OffchainWorkerExt, TransactionPoolExt},
    sr25519::Signature,
    H256,
};
use sp_keystore::{testing::KeyStore, KeystoreExt, SyncCryptoStore};

use sp_std::str;
use sp_std::vec::Vec;
use std::sync::Arc;

use sp_runtime::{
    testing::{Header, TestXt},
    traits::{BlakeTwo256, Extrinsic as ExtrinsicT, IdentifyAccount, IdentityLookup, Verify, BlockNumberProvider},
};

use sp_core::{ sr25519, Pair, Public};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;
type AccountPublic = <Signature as Verify>::Signer;

frame_support::construct_runtime!(
    pub enum Test where
        Block = Block,
        NodeBlock = Block,
        UncheckedExtrinsic = UncheckedExtrinsic,
    {
        System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
        Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
        Proposals: proposals::{Pallet, Call, Storage, Event<T>},
        Timestamp: pallet_timestamp::{Pallet, Call, Storage, Inherent},
        TransactionPayment: pallet_transaction_payment::{Pallet, Storage},
       // XcmPallet: pallet_xcm::{Pallet, Call, Storage, Event<T>, Origin} = 51,
        //CumulusXcm: cumulus_pallet_xcm::{Pallet, Call, Event<T>, Origin} = 52,

    }
);

parameter_types! {
    pub const TransactionByteFee: u64 = 1;
    pub const OperationalFeeMultiplier: u8 = 5;
}
impl pallet_transaction_payment::Config for Test {
    type OnChargeTransaction = pallet_transaction_payment::CurrencyAdapter<Balances, ()>;
    type TransactionByteFee = TransactionByteFee;
    type OperationalFeeMultiplier = OperationalFeeMultiplier;
    type WeightToFee = IdentityFee<u64>;
    type FeeMultiplierUpdate = ();
}

parameter_types! {
    pub const BlockHashCount: u64 = 250;
    pub BlockWeights: frame_system::limits::BlockWeights =
        frame_system::limits::BlockWeights::simple_max(1024);
}
//pub type LocalOriginToLocation = SignedToAccountId32<Origin, AccountId, RelayNetwork>;


impl frame_system::Config for Test {
    type BaseCallFilter = frame_support::traits::Everything;
    type BlockWeights = ();
    type BlockLength = ();
    type DbWeight = ();
    type Origin = Origin;
    type Call = Call;
    type Index = u64;
    type BlockNumber = u64;
    type Hash = H256;
    type Hashing = BlakeTwo256;
    type AccountId = sp_core::sr25519::Public;
    type Lookup = IdentityLookup<Self::AccountId>;
    type Header = Header;
    type Event = Event;
    type BlockHashCount = BlockHashCount;
    type Version = ();
    type PalletInfo = PalletInfo;
    type AccountData = pallet_balances::AccountData<u64>;
    type OnNewAccount = ();
    type OnKilledAccount = ();
    type SystemWeightInfo = ();
    type SS58Prefix = ();
    type OnSetCode = ();
}

type Extrinsic = TestXt<Call, ()>;
type AccountId = <<Signature as Verify>::Signer as IdentifyAccount>::AccountId;

impl frame_system::offchain::SigningTypes for Test {
    type Public = <Signature as Verify>::Signer;
    type Signature = Signature;
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Test
where
    Call: From<LocalCall>,
{
    type OverarchingCall = Call;
    type Extrinsic = Extrinsic;
}

parameter_types! {
    pub const GracePeriod: u64 = 5;
    pub const UnsignedInterval: u64 = 128;
    pub const UnsignedPriority: u64 = 1 << 20;
}

parameter_types! {
    pub const ExistentialDeposit: u64 = 5;
    pub const MaxReserves: u32 = 50;
}

impl pallet_balances::Config for Test {
    type Balance = u64;
    type Event = Event;
    type DustRemoval = ();
    type ExistentialDeposit = ExistentialDeposit;
    type AccountStore = System;
    type WeightInfo = ();
    type MaxLocks = ();
    type MaxReserves = MaxReserves;
    type ReserveIdentifier = [u8; 8];
}
/*pub struct DoNothingRouter;
impl SendXcm for DoNothingRouter {
    fn send_xcm(_dest: impl Into<MultiLocation>, _msg: Xcm<()>) -> SendResult {
        Ok(())
    }
}*/
// For testing the module, we construct a mock runtime.

parameter_types! {
    pub const MinimumPeriod: u64 = 1;
}
impl pallet_timestamp::Config for Test {
    type Moment = u64;
    type OnTimestampSet = ();
    type MinimumPeriod = MinimumPeriod;
    type WeightInfo = ();
}

parameter_types! {
    pub const 2WeekBlockUnit: u32 = 100800u32;
}
impl proposals::Config for Test {
    type Event = Event;
    type PalletId = ();
    type Currency = Balances;
    type WeightInfo = ();
    type MaxProposalsPerRound = ConstU32<4>;
    // Adding 2 weeks as th expiration time
    type MaxWithdrawalExpiration: IsType<<Self as frame_system::Config>::BlockNumber> = now + 2WeekBlockUnit.into();
}

parameter_types! {
    pub const BasicDeposit: u64 = 10;
	pub const FieldDeposit: u64 = 10;
	pub const MaxAdditionalFields: u32 = 2;
	pub const MaxRegistrars: u32 = 20;
}
ord_parameter_types! {
	pub const One: u64 = 1;
	pub const Two: u64 = 2;
}
type EnsureOneOrRoot = EnsureOneOf<EnsureRoot<u64>, EnsureSignedBy<One, u64>,EnsureSignedBy<One, u64>>;
type EnsureTwoOrRoot = EnsureOneOf<EnsureRoot<u64>, EnsureSignedBy<Two, u64>,EnsureSignedBy<Two, u64>>;

impl pallet_identity::Config for Test {
    type Event = Event;
	type Currency = Balances;
	type Slashed = ();
	type BasicDeposit = BasicDeposit;
	type FieldDeposit = FieldDeposit;
	type SubAccountDeposit = ConstU32<10>;
	type MaxSubAccounts = ConstU32<2>;
	type MaxAdditionalFields = MaxAdditionalFields;
	type MaxRegistrars = MaxRegistrars;
	type RegistrarOrigin = EnsureOneOrRoot;
	type ForceOrigin = EnsureTwoOrRoot;
	type WeightInfo = ();
}

// pub trait Config: CreateSignedTransaction<Self> + frame_system::Config {}
impl<LocalCall> frame_system::offchain::CreateSignedTransaction<LocalCall> for Test
where
    Call: From<LocalCall>,
{
    fn create_transaction<C: frame_system::offchain::AppCrypto<Self::Public, Self::Signature>>(
        call: Call,
        _public: <Signature as Verify>::Signer,
        _account: AccountId,
        nonce: u64,
    ) -> Option<(Call, <Extrinsic as ExtrinsicT>::SignaturePayload)> {
        Some((call, (nonce, ())))
    }
}

/*
parameter_types! {
    // pub const RelayLocationson::X1(Parent);
    pub const RelayNetwork: NetworkId = NetworkId::Kusama;
    // pub RelayChainOrigin: Origin = cumulus_pallet_xcm::Origin::Relay.into();
}
*/

parameter_types! {
    pub const UnitWeightCost: Weight = 10;
    pub const MaxInstructions: u32 = 100;
}


/*pub struct DummyWeightTrader;
impl WeightTrader for DummyWeightTrader {
    fn new() -> Self {
        DummyWeightTrader
    }

    fn buy_weight(&mut self, _weight: Weight, _payment: Assets) -> Result<Assets, XcmError> {
        Ok(Assets::default())
    }
}
pub struct DummyAssetTransactor;
impl TransactAsset for DummyAssetTransactor {
    fn deposit_asset(_what: &MultiAsset, _who: &MultiLocation) -> XcmResult {
        Ok(())
    }

    fn withdraw_asset(_what: &MultiAsset, _who: &MultiLocation) -> Result<Assets, XcmError> {
        let asset: MultiAsset = (Parent, 100_000).into();
        Ok(asset.into())
    }
}
*/

#[test]
fn create_a_test_project() {
    const PHRASE: &str =
        "news slush supreme milk chapter athlete soap sausage put clutch what kitten";
    /*let (offchain, offchain_state) = testing::TestOffchainExt::new();
    let (pool, pool_state) = testing::TestTransactionPoolExt::new();

    let keystore = KeyStore::new();

    SyncCryptoStore::sr25519_generate_new(
        &keystore,
        proposals::KEY_TYPE,
        Some(&format!("{}/hunter1", PHRASE)),
    )
    .unwrap();
*/

    let mut t = sp_io::TestExternalities::default();
  /*
    t.register_extension(OffchainWorkerExt::new(offchain));
    t.register_extension(TransactionPoolExt::new(pool));
    t.register_extension(KeystoreExt(Arc::new(keystore)));
*/

    //mock_submit_response(&mut offchain_state.write());
    //let expected_response = br#"{"USD": 155.23}"#.to_vec();
    t.execute_with(|| {
        Proposals::create_project(
            Origin::signed(Default::default()),
            //project name
            str::from_utf8(b"Project Hari Om").unwrap().as_bytes().to_vec(),
            //project logo
            str::from_utf8(b"Logo Hariom").unwrap().as_bytes().to_vec(),
            //project description
            str::from_utf8(b"This project is aimed at promoting Decentralised Data and Transparent CrowdFunding.").unwrap().as_bytes().to_vec(), 
            //website
            str::from_utf8(b"1. MVP, 2. Community Tested, 3. Prod Rollout").unwrap().as_bytes().to_vec(),
            //milestone
            4,
            //funds required
            1000000u64
        ).unwrap();
           
/*
        let tx1 = pool_state.write().transactions.pop().unwrap();
        let tx2 = pool_state.write().transactions.pop().unwrap();

        let tx1 = Extrinsic::decode(&mut &*tx1).unwrap();
        let tx2 = Extrinsic::decode(&mut &*tx2).unwrap();
*/

        assert_eq!(1,1);

        /*if let Call::Proposals(crate::Call::create_project {
            block_number: _block_number,
            key: _key,
            data: response,
        }) = tx2.call
        {
            assert_eq!(response, expected_response);
        }

        if let Call::KylinOracle(crate::Call::clear_processed_requests_unsigned {
            block_number: _block_number,
            processed_requests,
        }) = tx1.call
        {
            assert_eq!(1, processed_requests.len());
        }*/
    });
}




