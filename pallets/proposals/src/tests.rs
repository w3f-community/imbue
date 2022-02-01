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
use frame_support::{
    assert_noop,
    parameter_types, ord_parameter_types, PalletId,dispatch::DispatchErrorWithPostInfo,
    traits::{ConstU32},
    weights::{IdentityFee, PostDispatchInfo, Weight},
};

use frame_system::{EnsureRoot};
use sp_core::{
    sr25519::Signature,
    H256,
};

use sp_std::str;
use sp_std::vec::Vec;

use sp_runtime::{
    testing::{Header, TestXt},
    traits::{BlakeTwo256, Extrinsic as ExtrinsicT, IdentifyAccount, IdentityLookup, Verify},
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

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
        Identity: pallet_identity::{Pallet, Call, Storage, Event<T>},
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
    pub const TwoWeekBlockUnit: u32 = 100800u32;
    pub const ProposalsPalletId: PalletId = PalletId(*b"imbgrant");
}
impl proposals::Config for Test {
    type Event = Event;
    type PalletId = ProposalsPalletId;
    type Currency = Balances;
    type WeightInfo = ();
    type MaxProposalsPerRound = ConstU32<4>;
    // Adding 2 weeks as th expiration time
    type MaxWithdrawalExpiration = TwoWeekBlockUnit;
}


parameter_types! {
	pub const BasicDeposit: u64 = 10;
	pub const FieldDeposit: u64 = 10;
	pub const SubAccountDeposit: u64 = 10;
	pub const MaxSubAccounts: u32 = 2;
	pub const MaxAdditionalFields: u32 = 2;
	pub const MaxRegistrars: u32 = 20;
}
ord_parameter_types! {
	pub const One: u64 = 1;
	pub const Two: u64 = 2;
}

impl pallet_identity::Config for Test {
    type Event = Event;
	type Currency = Balances;
	type Slashed = ();
	type BasicDeposit = BasicDeposit;
	type FieldDeposit = FieldDeposit;
	type SubAccountDeposit = SubAccountDeposit;
	type MaxSubAccounts = MaxSubAccounts;
	type MaxAdditionalFields = MaxAdditionalFields;
	type MaxRegistrars = MaxRegistrars;
	type RegistrarOrigin = EnsureRoot<AccountId>;
	type ForceOrigin = EnsureRoot<AccountId>;
	type WeightInfo = ();
}

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

parameter_types! {
    pub const UnitWeightCost: Weight = 10;
    pub const MaxInstructions: u32 = 100;
}

#[test]
fn create_a_test_project() {
    let mut t = sp_io::TestExternalities::default();
    t.execute_with(|| {
        Proposals::create_project(
            Origin::signed(Default::default()),
            //project name
            str::from_utf8(b"Imbue's Awesome Initiative").unwrap().as_bytes().to_vec(),
            //project logo
            str::from_utf8(b"Imbue Logo").unwrap().as_bytes().to_vec(),
            //project description
            str::from_utf8(b"This project is aimed at promoting Decentralised Data and Transparent Crowdfunding.").unwrap().as_bytes().to_vec(), 
            //website
            str::from_utf8(b"https://imbue.network").unwrap().as_bytes().to_vec(),
            //milestone
            vec![ProposedMilestone { 
                name: Vec::new(), percentage_to_unlock: 100
            }],
            //funds required
            1000000u64
        ).unwrap();
    });
}




#[test]
fn create_a_test_project_with_less_than_100_percent() {
    let mut t = sp_io::TestExternalities::default();

    t.execute_with(|| {
        assert_noop!(
        Proposals::create_project(
            Origin::signed(Default::default()),
            //project name
            str::from_utf8(b"Imbue's Awesome Initiative").unwrap().as_bytes().to_vec(),
            //project logo
            str::from_utf8(b"Imbue Logo").unwrap().as_bytes().to_vec(),
            //project description
            str::from_utf8(b"This project is aimed at promoting Decentralised Data and Transparent Crowdfunding.").unwrap().as_bytes().to_vec(), 
            //website
            str::from_utf8(b"https://imbue.network").unwrap().as_bytes().to_vec(),
            //milestone
            vec![ProposedMilestone { 
                name: Vec::new(), percentage_to_unlock: 99
            }],
            //funds required
            1000000u64
        ),DispatchErrorWithPostInfo {
            post_info: PostDispatchInfo {
                actual_weight: None,
                pays_fee: Pays::Yes,
            },
            error: Error::<Test>::MilestonesTotalPercentageMustEqual100.into()
        }) ;
    });
}




