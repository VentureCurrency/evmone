// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2022 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0

#include <gmock/gmock.h>
#include <test/state/hash_utils.hpp>
#include <test/state/rlp.hpp>
#include <test/state/state.hpp>
#include <test/utils/utils.hpp>
#include <bit>

using namespace evmone;
using namespace evmc::literals;
using namespace intx;
using namespace testing;

static constexpr auto emptyBytesHash =
    0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470_bytes32;

static constexpr auto emptyMPTHash =
    0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_bytes32;

TEST(state_rlp, empty_bytes_hash)
{
    EXPECT_EQ(keccak256({}), emptyBytesHash);
}

TEST(state_rlp, empty_list_hash)
{
    EXPECT_EQ(keccak256(bytes{0xc0}), EmptyListHash);  // Hash of empty RLP list: 0xc0.
    EXPECT_EQ(keccak256(rlp::encode(std::vector<uint64_t>{})), EmptyListHash);
}

TEST(state_rlp, empty_mpt_hash)
{
    const auto rlp_null = rlp::encode(0);
    EXPECT_EQ(rlp_null, bytes{0x80});
    EXPECT_EQ(keccak256(rlp_null), emptyMPTHash);
}

TEST(state_rlp, encode_string_short)
{
    EXPECT_EQ(rlp::encode(0x01), "01"_hex);
    EXPECT_EQ(rlp::encode(0x31), "31"_hex);
    EXPECT_EQ(rlp::encode(0x7f), "7f"_hex);
}

TEST(state_rlp, encode_string_long)
{
    const auto buffer = std::make_unique<uint8_t[]>(0xffffff);

    const auto r1 = rlp::encode({buffer.get(), 0xaabb});
    EXPECT_EQ(r1.size(), 0xaabb + 3);
    EXPECT_EQ(hex({r1.data(), 10}), "b9aabb00000000000000");

    const auto r2 = rlp::encode({buffer.get(), 0xffff});
    EXPECT_EQ(r2.size(), 0xffff + 3);
    EXPECT_EQ(hex({r2.data(), 10}), "b9ffff00000000000000");

    const auto r3 = rlp::encode({buffer.get(), 0xaabbcc});
    EXPECT_EQ(r3.size(), 0xaabbcc + 4);
    EXPECT_EQ(hex({r3.data(), 10}), "baaabbcc000000000000");

    const auto r4 = rlp::encode({buffer.get(), 0xffffff});
    EXPECT_EQ(r4.size(), 0xffffff + 4);
    EXPECT_EQ(hex({r4.data(), 10}), "baffffff000000000000");
}

TEST(state_rlp, encode_c_array)
{
    const uint64_t a[]{1, 2, 3};
    EXPECT_EQ(hex(rlp::encode(a)), "c3010203");
}

TEST(state_rlp, encode_vector)
{
    const auto x = 0xe1e2e3e4e5e6e7d0d1d2d3d4d5d6d7c0c1c2c3c4c5c6c7b0b1b2b3b4b5b6b7_u256;
    EXPECT_EQ(
        rlp::encode(x), "9fe1e2e3e4e5e6e7d0d1d2d3d4d5d6d7c0c1c2c3c4c5c6c7b0b1b2b3b4b5b6b7"_hex);
    const std::vector<uint256> v(0xffffff / 32, x);
    const auto r = rlp::encode(v);
    EXPECT_EQ(r.size(), v.size() * 32 + 4);
}

TEST(state_rlp, encode_account_with_balance)
{
    const auto expected =
        "f8 44"
        "80"
        "01"
        "a0 56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
        "a0 c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"_hex;

    const auto r = rlp::encode_tuple(uint64_t{0}, 1_u256, emptyMPTHash, emptyBytesHash);
    EXPECT_EQ(r, expected);
}

TEST(state_rlp, encode_storage_value)
{
    const auto value = 0x00000000000000000000000000000000000000000000000000000000000001ff_bytes32;
    const auto xvalue = rlp::encode(rlp::trim(value));
    EXPECT_EQ(xvalue, "8201ff"_hex);
}

TEST(state_rlp, encode_mpt_node)
{
    const auto path = "2041"_hex;
    const auto value = "765f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f31"_hex;
    const auto node = rlp::encode_tuple(path, value);
    EXPECT_EQ(node, "e18220419d765f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f31"_hex);
}

struct CustomStruct
{
    uint64_t a;
    bytes b;
};

inline bytes rlp_encode(const CustomStruct& t)
{
    return rlp::encode_tuple(t.a, t.b);
}

TEST(state_rlp, encode_custom_struct)
{
    const CustomStruct t{1, {0x02, 0x03}};
    EXPECT_EQ(rlp::encode(t), "c4 01 820203"_hex);
}

TEST(state_rlp, encode_custom_struct_list)
{
    const std::vector<CustomStruct> v{{1, {0x02, 0x03}}, {4, {0x05, 0x06}}};
    EXPECT_EQ(rlp::encode(v), "ca c401820203 c404820506"_hex);
}

TEST(state_rlp, encode_uint64)
{
    EXPECT_EQ(rlp::encode(uint64_t{0}), "80"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{1}), "01"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0x7f}), "7f"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0x80}), "8180"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0x81}), "8181"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0xff}), "81ff"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0x0100}), "820100"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0xffff}), "82ffff"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0x010000}), "83010000"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0xffffff}), "83ffffff"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0x01000000}), "8401000000"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0xffffffff}), "84ffffffff"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0x0100000000}), "850100000000"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0xffffffffff}), "85ffffffffff"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0x010000000000}), "86010000000000"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0xffffffffffff}), "86ffffffffffff"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0x01000000000000}), "8701000000000000"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0xffffffffffffff}), "87ffffffffffffff"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0x0100000000000000}), "880100000000000000"_hex);
    EXPECT_EQ(rlp::encode(uint64_t{0xffffffffffffffff}), "88ffffffffffffffff"_hex);
}

inline bytes to_significant_be_bytes(uint64_t x)
{
    const auto byte_width = (std::bit_width(x) + 7) / 8;
    const auto leading_zero_bits = std::countl_zero(x) & ~7;  // Leading bits rounded down to 8x.
    const auto trimmed_x = x << leading_zero_bits;            // Significant bytes moved to the top.

    uint8_t b[sizeof(x)];
    intx::be::store(b, trimmed_x);
    return bytes{b, static_cast<size_t>(byte_width)};
}

/// The "custom" implementation of RLP encoding of uint64. It trims leading zero bytes and
/// manually constructs bytes with variadic-length encoding.
inline bytes rlp_encode_uint64(uint64_t x)
{
    static constexpr uint8_t ShortBase = 0x80;
    if (x < ShortBase)  // Single-byte encoding.
        return bytes{(x == 0) ? ShortBase : static_cast<uint8_t>(x)};

    const auto b = to_significant_be_bytes(x);
    return static_cast<uint8_t>(ShortBase + b.size()) + b;
}

TEST(state_rlp, encode_uint64_custom)
{
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0}), "80"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{1}), "01"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0x7f}), "7f"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0x80}), "8180"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0x81}), "8181"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0xff}), "81ff"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0x0100}), "820100"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0xffff}), "82ffff"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0x010000}), "83010000"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0xffffff}), "83ffffff"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0x01000000}), "8401000000"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0xffffffff}), "84ffffffff"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0x0100000000}), "850100000000"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0xffffffffff}), "85ffffffffff"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0x010000000000}), "86010000000000"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0xffffffffffff}), "86ffffffffffff"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0x01000000000000}), "8701000000000000"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0xffffffffffffff}), "87ffffffffffffff"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0x0100000000000000}), "880100000000000000"_hex);
    EXPECT_EQ(rlp_encode_uint64(uint64_t{0xffffffffffffffff}), "88ffffffffffffffff"_hex);
}

TEST(state_rlp, tx_to_rlp_legacy)
{
    // Example from
    // https://eips.ethereum.org/EIPS/eip-155

    state::Transaction tx{};
    tx.type = evmone::state::Transaction::Type::legacy;
    tx.data = ""_b;
    tx.gas_limit = 21000;
    tx.max_gas_price = 20000000000;
    tx.max_priority_gas_price = 20000000000;
    tx.sender = 0x0000000000000000000000000000000000000000_address;
    tx.to = 0x3535353535353535353535353535353535353535_address;
    tx.value = 1000000000000000000_u256;
    tx.access_list = {};
    tx.nonce = 9;
    tx.r = {};
    tx.s = {};
    tx.v = 1;
    tx.chain_id = 1;

    const auto rlp_rep = rlp::encode(tx);
    EXPECT_EQ(rlp_rep,
        "ec"
        "09"
        "8504a817c800"
        "825208"
        "943535353535353535353535353535353535353535"
        "880de0b6b3a7640000"
        "80"
        "01"
        "80"
        "80"_hex);
}

TEST(state_rlp, tx_to_rlp_legacy_with_data)
{
    // Example from
    // https://etherscan.io/tx/0x033e9f8db737193d4666911a164e218d58d80edc64f4ed393d0c48c1ce2673e7

    state::Transaction tx{};
    tx.type = evmone::state::Transaction::Type::legacy;
    tx.data = "0xa0712d680000000000000000000000000000000000000000000000000000000000000003"_hex;
    tx.gas_limit = 421566;
    tx.max_gas_price = 14829580649;
    tx.max_priority_gas_price = 14829580649;
    tx.sender = 0xc9d955665d6f90ef483a1ac0bd2443c17a550db7_address;
    tx.to = 0x963eda46936b489f4a0d153c20e47653d8bbf222_address;
    tx.value = 480000000000000000_u256;
    tx.access_list = {};
    tx.nonce = 0;
    tx.r = 0x3bcaa4f1603d2b3ebe6126f57e0ddefc6c6c58d8bbef7f3b29e14a915bf1828d_u256;
    tx.s = 0x00f37b7a0b6007ef4335a35198485e443051d45b42fea8bacc054721ecccdb5f_u256;
    tx.v = 27;
    tx.chain_id = 1;

    const auto rlp_rep = rlp::encode(tx);
    EXPECT_EQ(rlp_rep,
        "f890"
        "80"
        "850373e97169"
        "83066ebe"
        "94963eda46936b489f4a0d153c20e47653d8bbf222"
        "8806a94d74f4300000"
        "a4a0712d680000000000000000000000000000000000000000000000000000000000000003"
        "1b"
        "a03bcaa4f1603d2b3ebe6126f57e0ddefc6c6c58d8bbef7f3b29e14a915bf1828d"
        "9ff37b7a0b6007ef4335a35198485e443051d45b42fea8bacc054721ecccdb5f"_hex);

    EXPECT_EQ(keccak256(rlp_rep),
        0x033e9f8db737193d4666911a164e218d58d80edc64f4ed393d0c48c1ce2673e7_bytes32);
}

TEST(state_rlp, tx_to_rlp_eip1559)
{
    // Example from
    // https://etherscan.io/tx/0xee8d0f04073a6792b1bd6b1cb0b88cb57984905979d2668f84b9c3dcb8894da6

    state::Transaction tx{};

    tx.type = evmone::state::Transaction::Type::eip1559;
    tx.data = ""_b;
    tx.gas_limit = 30000;
    tx.max_gas_price = 14237787676;
    tx.max_priority_gas_price = 0;
    tx.sender = 0x95222290dd7278aa3ddd389cc1e1d165cc4bafe5_address;
    tx.to = 0x535b918f3724001fd6fb52fcc6cbc220592990a3_address;
    tx.value = 73360267083380739_u256;
    tx.access_list = {};
    tx.nonce = 132949;
    tx.r = 0x2fe690e16de3534bee626150596573d57cb56d0c2e48a02f64c0a03c1636ce2a_u256;
    tx.s = 0x4814f3dc7dac2ee153a2456aa3968717af7400972167dfb00b1cce1c23b6dd9f_u256;
    tx.v = 1;
    tx.chain_id = 1;

    const auto rlp_rep = rlp::encode(tx);
    EXPECT_EQ(rlp_rep,
        "02"
        "f872"
        "01"
        "83020755"
        "80"
        "850350a3661c"
        "827530"
        "94535b918f3724001fd6fb52fcc6cbc220592990a3"
        "880104a0c63421f803"
        "80"
        "c0"
        "01"
        "a02fe690e16de3534bee626150596573d57cb56d0c2e48a02f64c0a03c1636ce2a"
        "a04814f3dc7dac2ee153a2456aa3968717af7400972167dfb00b1cce1c23b6dd9f"_hex);

    EXPECT_EQ(keccak256(rlp_rep),
        0xee8d0f04073a6792b1bd6b1cb0b88cb57984905979d2668f84b9c3dcb8894da6_bytes32);
}

TEST(state_rlp, tx_to_rlp_eip1559_with_data)
{
    // Example taken from
    // https://etherscan.io/tx/0xf9400dd4722908fa7b8d514429aebfd4cd04aaa9faaf044554d2f550422baef9

    state::Transaction tx{};
    tx.type = evmone::state::Transaction::Type::eip1559;
    tx.data =
        "095ea7b3"
        "0000000000000000000000001111111254eeb25477b68fb85ed929f73a960582"
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"_hex;
    tx.gas_limit = 53319;
    tx.max_gas_price = 14358031378;
    tx.max_priority_gas_price = 576312105;
    tx.sender = 0xb24df1ff03fa211458fbd855d08b3d21704bdf2d_address;
    tx.to = 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2_address;
    tx.value = 0;
    tx.access_list = {};
    tx.nonce = 47;
    tx.r = 0x67d25d27169ab09afb516849b85ae96d51e1dfc0853257b2b7401a73cef2b08b_u256;
    tx.s = 0x3d8162a0f285284e02ed4ff387435c2742235a0534964f9b1415d4d10f28ce06_u256;
    tx.v = 1;
    tx.chain_id = 1;

    const auto rlp_rep = rlp::encode(tx);
    EXPECT_EQ(rlp_rep,
        "02"
        "f8b0"
        "012f"
        "842259d329"
        "850357ce2c12"
        "82d047"
        "94c02aaa39b223fe8d0a0e5c4f27ead9083c756cc2"
        "80"
        "b844095ea7b30000000000000000000000001111111254eeb25477b68fb85ed929f73a9"
        "60582ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
        "c0"
        "01a067d25d27169ab09afb516849b85ae96d51e1dfc0853257b2b7401a73cef2b08b"
        "a03d8162a0f285284e02ed4ff387435c2742235a0534964f9b1415d4d10f28ce06"_hex);

    EXPECT_EQ(keccak256(rlp_rep),
        0xf9400dd4722908fa7b8d514429aebfd4cd04aaa9faaf044554d2f550422baef9_bytes32);
}

TEST(state_rlp, tx_to_rlp_eip1559_invalid_v_value)
{
    state::Transaction tx{};
    tx.type = evmone::state::Transaction::Type::eip1559;
    tx.data = ""_hex;
    tx.gas_limit = 1;
    tx.max_gas_price = 1;
    tx.max_priority_gas_price = 1;
    tx.sender = 0x0000000000000000000000000000000000000000_address;
    tx.to = 0x0000000000000000000000000000000000000000_address;
    tx.value = 0;
    tx.access_list = {};
    tx.nonce = 47;
    tx.r = 0x0000000000000000000000000000000000000000000000000000000000000000_u256;
    tx.s = 0x0000000000000000000000000000000000000000000000000000000000000000_u256;
    tx.v = 2;
    tx.chain_id = 1;

    EXPECT_THAT([tx]() { rlp::encode(tx); },
        ThrowsMessage<std::invalid_argument>("`v` value for eip1559 transaction must be 0 or 1"));
}

TEST(state_rlp, tx_to_rlp_eip2930_invalid_v_value)
{
    state::Transaction tx{};
    tx.type = evmone::state::Transaction::Type::access_list;
    tx.data = ""_hex;
    tx.gas_limit = 1;
    tx.max_gas_price = 1;
    tx.max_priority_gas_price = 1;
    tx.sender = 0x0000000000000000000000000000000000000000_address;
    tx.to = 0x0000000000000000000000000000000000000000_address;
    tx.value = 0;
    tx.access_list = {};
    tx.nonce = 47;
    tx.r = 0x0000000000000000000000000000000000000000000000000000000000000000_u256;
    tx.s = 0x0000000000000000000000000000000000000000000000000000000000000000_u256;
    tx.v = 2;
    tx.chain_id = 1;

    EXPECT_THAT([tx]() { rlp::encode(tx); },
        ThrowsMessage<std::invalid_argument>("`v` value for eip2930 transaction must be 0 or 1"));
}

TEST(state_rlp, tx_to_rlp_eip1559_with_non_empty_access_list)
{
    state::Transaction tx{};
    tx.type = evmone::state::Transaction::Type::eip1559;
    tx.data = "00"_hex;
    tx.gas_limit = 0x3d0900;
    tx.max_gas_price = 0x7d0;
    tx.max_priority_gas_price = 0xa;
    tx.sender = 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address;
    tx.to = 0xcccccccccccccccccccccccccccccccccccccccc_address;
    tx.value = 0;
    tx.access_list = {{0xcccccccccccccccccccccccccccccccccccccccc_address,
        {0x0000000000000000000000000000000000000000000000000000000000000000_bytes32,
            0x0000000000000000000000000000000000000000000000000000000000000001_bytes32}}};
    tx.nonce = 1;
    tx.r = 0xd671815898b8dd34321adbba4cb6a57baa7017323c26946f3719b00e70c755c2_u256;
    tx.s = 0x3528b9efe3be57ea65a933d1e6bbf3b7d0c78830138883c1201e0c641fee6464_u256;
    tx.v = 0;
    tx.chain_id = 1;

    EXPECT_EQ(keccak256(rlp::encode(tx)),
        0xfb18421827800adcf465688e303cc9863045fdb96971473a114677916a3a08a4_bytes32);
}

TEST(state_rlp, tx_to_rlp_eip2930_with_non_empty_access_list)
{
    // https://etherscan.io/tx/0xf076e75aa935552e20e5d9fd4d1dda4ff33399ff3d6ac22843ae646f82c385d4

    state::Transaction tx{};
    tx.type = evmone::state::Transaction::Type::access_list;
    tx.data =
        "0x095ea7b3000000000000000000000000f17d23136b4fead139f54fb766c8795faae09660ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"_hex;
    tx.gas_limit = 51253;
    tx.max_gas_price = 15650965396;
    tx.max_priority_gas_price = 15650965396;
    tx.sender = 0xcb0b99284784d9e400b1020b01fc40ff193d3540_address;
    tx.to = 0x9232a548dd9e81bac65500b5e0d918f8ba93675c_address;
    tx.value = 0;
    tx.access_list = {{0x9232a548dd9e81bac65500b5e0d918f8ba93675c_address,
        {0x8e947fe742892ee6fffe7cfc013acac35d33a3892c58597344bed88b21eb1d2f_bytes32}}};
    tx.nonce = 62;
    tx.r = 0x2cfaa5ffa42172bfa9f83207a257c53ba3a106844ee58e9131466f655ecc11e9_u256;
    tx.s = 0x419366dadd905a16cd433f2953f9ed976560822bb2611ac192b939f7b9c2a98c_u256;
    tx.v = 1;
    tx.chain_id = 1;

    EXPECT_EQ(keccak256(rlp::encode(tx)),
        0xf076e75aa935552e20e5d9fd4d1dda4ff33399ff3d6ac22843ae646f82c385d4_bytes32);
}

template <typename T>
T decode_helper(const std::string& hex_str)
{
    T to{};
    const auto from = from_hex(hex_str);
    if (from.has_value())
    {
        auto bv = bytes_view(*from);
        rlp::decode(bv, to);
    }

    return to;
}

TEST(state_rlp, unsinged_int_loading)
{
    EXPECT_EQ(rlp::load<uint64_t>("0x0102030405060708"_hex), 0x0102030405060708);

    EXPECT_THAT([&] { (void)rlp::load<uint64_t>("0x010203040506070809"_hex); },
        ThrowsMessage<std::runtime_error>("load: input too big"));
}

TEST(rlp, decode_simple)
{
    EXPECT_EQ(decode_helper<uint8_t>("0x03"), 3);
    EXPECT_EQ(decode_helper<uint16_t>("0x03"), 3);
    EXPECT_EQ(decode_helper<uint32_t>("0x03"), 3);
    EXPECT_EQ(decode_helper<uint64_t>("0x03"), 3);
    EXPECT_EQ(decode_helper<uint128>("0x03"), 3);
    EXPECT_EQ(decode_helper<uint256>("0x03"), 3);
    EXPECT_EQ(decode_helper<uint512>("0x03"), 3);

    EXPECT_EQ(decode_helper<uint16_t>("0x8203E8"), 1000);
    EXPECT_EQ(decode_helper<uint32_t>("0x8203E8"), 1000);
    EXPECT_EQ(decode_helper<uint128>("0x8203E8"), 1000);
    EXPECT_EQ(decode_helper<uint256>("0x8203E8"), 1000);
    EXPECT_EQ(decode_helper<uint512>("0x8203E8"), 1000);

    EXPECT_EQ(decode_helper<uint256>(
                  "0xA00102030405060708091011121314151617181920212223242526272829303132"),
        0x0102030405060708091011121314151617181920212223242526272829303132_u256);

    EXPECT_EQ(decode_helper<uint512>(
                  "0xb8400102030405060708091011121314151617181920212223242526272829303132"
                  "3334353637383940414243444546474849505152535455565758596061626364"),
        0x01020304050607080910111213141516171819202122232425262728293031323334353637383940414243444546474849505152535455565758596061626364_u512);

    EXPECT_EQ(decode_helper<std::vector<uint8_t>>("0xc20304"), (std::vector<uint8_t>{3, 4}));
    EXPECT_EQ(decode_helper<bytes>("0x820301"), (bytes{3, 1}));

    EXPECT_EQ(decode_helper<address>("0x940102030405060708091011121314151617181920"),
        0x0102030405060708091011121314151617181920_address);

    EXPECT_EQ((decode_helper<std::pair<uint8_t, uint64_t>>("0xc20304")),
        (std::pair<uint8_t, uint64_t>{3, 4}));
}

TEST(rlp, decode_error)
{
    EXPECT_THAT([&] { decode_helper<uint8_t>(""); },
        ThrowsMessage<std::runtime_error>("rlp decoding error: input is empty"));

    EXPECT_THAT([&] { decode_helper<uint16_t>("0x8203"); },
        ThrowsMessage<std::runtime_error>("rlp decoding error: input too short"));

    EXPECT_THAT([&] { decode_helper<uint16_t>("0xb903"); },
        ThrowsMessage<std::runtime_error>("rlp decoding error: input too short"));

    EXPECT_THAT(
        [&] {
            decode_helper<uint512>(
                "0xb8400102030405060708091011121314151617181920212223242526272829303132"
                "33343536373839404142434445464748495051525354555657585960616263");
        },
        ThrowsMessage<std::runtime_error>("rlp decoding error: input too short"));

    EXPECT_THAT(
        [&] {
            decode_helper<intx::uint<2048>>(
                "0xb90100"
                "0102030405060708091011121314151617181920212223242526272829303132"
                "3334353637383940414243444546474849505152535455565758596061626364"
                "0102030405060708091011121314151617181920212223242526272829303132"
                "3334353637383940414243444546474849505152535455565758596061626364"
                "0102030405060708091011121314151617181920212223242526272829303132"
                "3334353637383940414243444546474849505152535455565758596061626364"
                "0102030405060708091011121314151617181920212223242526272829303132"
                "33343536373839404142434445464748495051525354555657585960616263");
        },
        ThrowsMessage<std::runtime_error>("rlp decoding error: input too short"));

    EXPECT_THAT([&] { decode_helper<std::vector<uint8_t>>("0xc203"); },
        ThrowsMessage<std::runtime_error>("rlp decoding error: input too short"));

    EXPECT_THAT([&] { decode_helper<std::vector<uint8_t>>("0xf903"); },
        ThrowsMessage<std::runtime_error>("rlp decoding error: input too short"));

    EXPECT_THAT(
        [&] {
            decode_helper<std::vector<uint8_t>>(
                "0xf90100"
                "0102030405060708091011121314151617181920212223242526272829303132"
                "3334353637383940414243444546474849505152535455565758596061626364"
                "0102030405060708091011121314151617181920212223242526272829303132"
                "3334353637383940414243444546474849505152535455565758596061626364"
                "0102030405060708091011121314151617181920212223242526272829303132"
                "3334353637383940414243444546474849505152535455565758596061626364"
                "0102030405060708091011121314151617181920212223242526272829303132"
                "33343536373839404142434445464748495051525354555657585960616263");
        },
        ThrowsMessage<std::runtime_error>("rlp decoding error: input too short"));

    EXPECT_THAT([&] { decode_helper<bytes>("0xc20301"); },
        ThrowsMessage<std::runtime_error>("rlp decoding error: unexpected list type"));

    EXPECT_THAT([&] { decode_helper<uint16_t>("0x83030201"); },
        ThrowsMessage<std::runtime_error>("rlp decoding error: unexpected type"));

    EXPECT_THAT([&] { decode_helper<uint16_t>("0xc20301"); },
        ThrowsMessage<std::runtime_error>("rlp decoding error: unexpected list type"));

    EXPECT_THAT([&] { decode_helper<address>("0xD40102030405060708091011121314151617181920"); },
        ThrowsMessage<std::runtime_error>("rlp decoding error: unexpected list type"));

    EXPECT_THAT([&] { decode_helper<std::vector<uint8_t>>("0x820301"); },
        ThrowsMessage<std::runtime_error>("rlp decoding error: unexpected type. list expected"));

    EXPECT_THAT([&] { (decode_helper<std::pair<uint8_t, uint64_t>>("0x820304")); },
        ThrowsMessage<std::runtime_error>("rlp decoding error: unexpected type. list expected"));

    EXPECT_THAT([&] { decode_helper<address>("0x95010203040506070809101112131415161718192021"); },
        ThrowsMessage<std::runtime_error>("rlp decoding error: payload too big"));
}

TEST(state_rlp, decode_eip1559)
{
    // https://sepolia.etherscan.io/tx/0x8e35aa725df0dac49303324d2315f8a31b1c40fcd42e5b7839a3b78e58ff7b52

    const auto input =
        "0x02f87883aa36a782993c8477359400852e90edd00082520894b2b7174595d042cbec11d9e71df6f6b07ab912"
        "71881bafa9ee16e7800080c080a0102d8426eae3027b62a74a81e09c570af6cd8a79dcf819ab79fd845a867d4e"
        "64a03b1c7eaa931012815784f39d139cb24e6f9e75cd903dde47ab29da98eee7c0ff"_hex;

    state::Transaction tx;
    auto bv = bytes_view{input};
    rlp::decode(bv, tx);

    EXPECT_EQ(tx.chain_id, 11155111);
    EXPECT_EQ(tx.nonce, 39228);
    EXPECT_EQ(tx.max_priority_gas_price, 2000000000);
    EXPECT_EQ(tx.max_gas_price, 200000000000);
    EXPECT_EQ(tx.gas_limit, 21000);
    EXPECT_EQ(tx.to, 0xb2b7174595d042cbec11d9e71df6f6b07ab91271_address);
    EXPECT_EQ(tx.value, 1995000000000000000);
    EXPECT_EQ(tx.data, bytes());
    EXPECT_EQ(tx.access_list, state::AccessList{});
    EXPECT_EQ(tx.v, 0);
    EXPECT_EQ(tx.r, 0x102d8426eae3027b62a74a81e09c570af6cd8a79dcf819ab79fd845a867d4e64_u256);
    EXPECT_EQ(tx.s, 0x3b1c7eaa931012815784f39d139cb24e6f9e75cd903dde47ab29da98eee7c0ff_u256);
}

TEST(state_rlp, decode_eip1559_with_data)
{
    // https://sepolia.etherscan.io/tx/0xd9fd2faba25978a9af401418bd4a6c31f50af0e4b243746af6c44ff4a61e909d

    const auto input =
        "0x02f8f483aa36a78242e68459682f008459682f0e82962494d0f723c6b2226df56fe41e63b9eaa66eb540bcb8"
        "80b884abac047b0000000000000000000000000000000000000000000000000000000000fe5f25d289f0fc646b"
        "735f24409f6b5c41f0ab2ee279c9676f60ef958a537cd67c7c3e80000000000000000000000000000000000000"
        "000000000000000000001a0e8b8322f0645f57da2d65a174644c2855d145395daafcdec72018405167bb31c0af"
        "c001a05b2846d2555b0c5eed39603732290ef320dca6ee4f0a399e193fe628592fe99da04e19a7efb8a4ac5ca3"
        "619acd6de8c57611e4289955f028664aac42f7a57a4b5e"_hex;

    state::Transaction tx;
    auto bv = bytes_view{input};
    rlp::decode(bv, tx);

    EXPECT_EQ(tx.chain_id, 11155111);
    EXPECT_EQ(tx.nonce, 17126);
    EXPECT_EQ(tx.max_priority_gas_price, 1500000000);
    EXPECT_EQ(tx.max_gas_price, 1500000014);
    EXPECT_EQ(tx.gas_limit, 38436);
    EXPECT_EQ(tx.to, 0xd0f723c6b2226df56fe41e63b9eaa66eb540bcb8_address);
    EXPECT_EQ(tx.value, 0);
    EXPECT_EQ(tx.data,
        "0xabac047b0000000000000000000000000000000000000000000000000000000000fe5f25d289f0fc646b735f"
        "24409f6b5c41f0ab2ee279c9676f60ef958a537cd67c7c3e800000000000000000000000000000000000000000"
        "00000000000000001a0e8b8322f0645f57da2d65a174644c2855d145395daafcdec72018405167bb31c0af"
        ""_hex);
    EXPECT_EQ(tx.access_list, state::AccessList{});
    EXPECT_EQ(tx.v, 1);
    EXPECT_EQ(tx.r, 0x5b2846d2555b0c5eed39603732290ef320dca6ee4f0a399e193fe628592fe99d_u256);
    EXPECT_EQ(tx.s, 0x4e19a7efb8a4ac5ca3619acd6de8c57611e4289955f028664aac42f7a57a4b5e_u256);
}

TEST(state_rlp, decode_legacy)
{
    // https://sepolia.etherscan.io/tx/0x3d5ed47bf255e67602a12f7d44cf215a83cad4aef5195e7700707233ff7437dd

    const auto input =
        "0xf87082cbc584ae0baa0082520894611e4a6f03bd0a1c2ff483f4c2cb1c0c6da6eed1872386f26fc100008084"
        "01546d71a0612617dc772e3170b3d65363849e97e4c96c63596a6b4c0d208babce80527aa1a01df2f3207e9c10"
        "35384ec77ab12a55be9f5a7ce3fe456b814cd8d95d7e07e41f"_hex;

    state::Transaction tx;
    auto bv = bytes_view{input};
    rlp::decode(bv, tx);

    EXPECT_EQ(tx.chain_id, 11155111);
    EXPECT_EQ(tx.nonce, 52165);
    EXPECT_EQ(tx.max_priority_gas_price, 2920000000);
    EXPECT_EQ(tx.max_gas_price, 2920000000);
    EXPECT_EQ(tx.gas_limit, 21000);
    EXPECT_EQ(tx.to, 0x611e4a6f03bd0a1c2ff483f4c2cb1c0c6da6eed1_address);
    EXPECT_EQ(tx.value, 10000000000000000);
    EXPECT_EQ(tx.data, bytes());
    EXPECT_EQ(tx.v, 0);
    EXPECT_EQ(tx.r, 0x612617dc772e3170b3d65363849e97e4c96c63596a6b4c0d208babce80527aa1_u256);
    EXPECT_EQ(tx.s, 0x1df2f3207e9c1035384ec77ab12a55be9f5a7ce3fe456b814cd8d95d7e07e41f_u256);
}

TEST(state_rlp, decode_legacy_with_data)
{
    // https://sepolia.etherscan.io/tx/0x7f7b1d6fe0797374f6a65a5fd7771c6691fa38497f5773207e649a1271e48554

    const auto input =
        "0xf8b083016b40843b9aca008307a120945c7a6cf20cbd3eef32e19b9cad4eca17c432a79480b844202ee0ed00"
        "0000000000000000000000000000000000000000000000000000000000172f0000000000000000000000000000"
        "00000000000000000000000000009ac790d08401546d72a02c9688636199d0a2c5965aa9380f764b70f2fc1d29"
        "3164d71c2d66649a955b6da00139f9afc4885673c6b9d1b2d33afc5c3867c362ae55357a3b8038ed164ccad4"
        ""_hex;

    state::Transaction tx;
    auto bv = bytes_view{input};
    rlp::decode(bv, tx);

    EXPECT_EQ(tx.chain_id, 11155111);  // For legacy tx chain id in encoded in v value.
    EXPECT_EQ(tx.nonce, 92992);
    EXPECT_EQ(tx.max_priority_gas_price, 1000000000);
    EXPECT_EQ(tx.max_gas_price, 1000000000);
    EXPECT_EQ(tx.gas_limit, 500000);
    EXPECT_EQ(tx.to, 0x5c7a6cf20cbd3eef32e19b9cad4eca17c432a794_address);
    EXPECT_EQ(tx.value, 0);
    EXPECT_EQ(tx.data,
        "0x202ee0ed000000000000000000000000000000000000000000000000000000000000172f0000000000000000"
        "00000000000000000000000000000000000000009ac790d0"_hex);
    EXPECT_EQ(tx.v, 1);
    EXPECT_EQ(tx.r, 0x2c9688636199d0a2c5965aa9380f764b70f2fc1d293164d71c2d66649a955b6d_u256);
    EXPECT_EQ(tx.s, 0x0139f9afc4885673c6b9d1b2d33afc5c3867c362ae55357a3b8038ed164ccad4_u256);
}

TEST(state_rlp, decode_access_list_with_data)
{
    // https://etherscan.io/tx/0xf076e75aa935552e20e5d9fd4d1dda4ff33399ff3d6ac22843ae646f82c385d4

    const auto input =
        "0x01f8e4013e8503a4dec79482c835949232a548dd9e81bac65500b5e0d918f8ba93675c80b844095ea7b30000"
        "00000000000000000000f17d23136b4fead139f54fb766c8795faae09660ffffffffffffffffffffffffffffff"
        "fffffffffffffffffffffffffffffffffff838f7949232a548dd9e81bac65500b5e0d918f8ba93675ce1a08e94"
        "7fe742892ee6fffe7cfc013acac35d33a3892c58597344bed88b21eb1d2f01a02cfaa5ffa42172bfa9f83207a2"
        "57c53ba3a106844ee58e9131466f655ecc11e9a0419366dadd905a16cd433f2953f9ed976560822bb2611ac192"
        "b939f7b9c2a98c"_hex;

    state::Transaction tx;
    auto bv = bytes_view{input};
    rlp::decode(bv, tx);

    EXPECT_EQ(tx.type, evmone::state::Transaction::Type::access_list);
    EXPECT_EQ(tx.data,
        "0x095ea7b3000000000000000000000000f17d23136b4fead139f54fb766c8795faae09660ffffffffffffffff"
        "ffffffffffffffffffffffffffffffffffffffffffffffff"_hex);
    EXPECT_EQ(tx.gas_limit, 51253);
    EXPECT_EQ(tx.max_gas_price, 15650965396);
    EXPECT_EQ(tx.max_priority_gas_price, 15650965396);
    EXPECT_EQ(tx.to, 0x9232a548dd9e81bac65500b5e0d918f8ba93675c_address);
    EXPECT_EQ(tx.value, 0);
    EXPECT_EQ(tx.access_list[0].first, 0x9232a548dd9e81bac65500b5e0d918f8ba93675c_address);
    EXPECT_EQ(tx.access_list[0].second[0],
        0x8e947fe742892ee6fffe7cfc013acac35d33a3892c58597344bed88b21eb1d2f_bytes32);
    EXPECT_EQ(tx.nonce, 62);
    EXPECT_EQ(tx.r, 0x2cfaa5ffa42172bfa9f83207a257c53ba3a106844ee58e9131466f655ecc11e9_u256);
    EXPECT_EQ(tx.s, 0x419366dadd905a16cd433f2953f9ed976560822bb2611ac192b939f7b9c2a98c_u256);
    EXPECT_EQ(tx.v, 1);
    EXPECT_EQ(tx.chain_id, 1);
}

TEST(state_rlp, decode_transaction_list)
{
    const auto tx0 =
        "f8b083016b40843b9aca008307a120945c7a6cf20cbd3eef32e19b9cad4eca17c432a79480b844202ee0ed00"
        "0000000000000000000000000000000000000000000000000000000000172f0000000000000000000000000000"
        "00000000000000000000000000009ac790d08401546d72a02c9688636199d0a2c5965aa9380f764b70f2fc1d29"
        "3164d71c2d66649a955b6da00139f9afc4885673c6b9d1b2d33afc5c3867c362ae55357a3b8038ed164ccad4";

    const auto tx1 =
        "01f8e4013e8503a4dec79482c835949232a548dd9e81bac65500b5e0d918f8ba93675c80b844095ea7b30000"
        "00000000000000000000f17d23136b4fead139f54fb766c8795faae09660ffffffffffffffffffffffffffffff"
        "fffffffffffffffffffffffffffffffffff838f7949232a548dd9e81bac65500b5e0d918f8ba93675ce1a08e94"
        "7fe742892ee6fffe7cfc013acac35d33a3892c58597344bed88b21eb1d2f01a02cfaa5ffa42172bfa9f83207a2"
        "57c53ba3a106844ee58e9131466f655ecc11e9a0419366dadd905a16cd433f2953f9ed976560822bb2611ac192"
        "b939f7b9c2a98c";

    const auto input = std::string("0xf90199") + tx0 + tx1;

    auto txs = decode_helper<std::vector<state::Transaction>>(input);

    EXPECT_EQ(txs[0].chain_id, 11155111);  // For legacy tx chain id in encoded in v value.
    EXPECT_EQ(txs[0].nonce, 92992);
    EXPECT_EQ(txs[0].max_priority_gas_price, 1000000000);
    EXPECT_EQ(txs[0].max_gas_price, 1000000000);
    EXPECT_EQ(txs[0].gas_limit, 500000);
    EXPECT_EQ(txs[0].to, 0x5c7a6cf20cbd3eef32e19b9cad4eca17c432a794_address);
    EXPECT_EQ(txs[0].value, 0);
    EXPECT_EQ(txs[0].data,
        "0x202ee0ed000000000000000000000000000000000000000000000000000000000000172f0000000000000000"
        "00000000000000000000000000000000000000009ac790d0"_hex);
    EXPECT_EQ(txs[0].v, 1);
    EXPECT_EQ(txs[0].r, 0x2c9688636199d0a2c5965aa9380f764b70f2fc1d293164d71c2d66649a955b6d_u256);
    EXPECT_EQ(txs[0].s, 0x0139f9afc4885673c6b9d1b2d33afc5c3867c362ae55357a3b8038ed164ccad4_u256);

    EXPECT_EQ(txs[1].type, evmone::state::Transaction::Type::access_list);
    EXPECT_EQ(txs[1].data,
        "0x095ea7b3000000000000000000000000f17d23136b4fead139f54fb766c8795faae09660ffffffffffffffff"
        "ffffffffffffffffffffffffffffffffffffffffffffffff"_hex);
    EXPECT_EQ(txs[1].gas_limit, 51253);
    EXPECT_EQ(txs[1].max_gas_price, 15650965396);
    EXPECT_EQ(txs[1].max_priority_gas_price, 15650965396);
    EXPECT_EQ(txs[1].to, 0x9232a548dd9e81bac65500b5e0d918f8ba93675c_address);
    EXPECT_EQ(txs[1].value, 0);
    EXPECT_EQ(txs[1].access_list[0].first, 0x9232a548dd9e81bac65500b5e0d918f8ba93675c_address);
    EXPECT_EQ(txs[1].access_list[0].second[0],
        0x8e947fe742892ee6fffe7cfc013acac35d33a3892c58597344bed88b21eb1d2f_bytes32);
    EXPECT_EQ(txs[1].nonce, 62);
    EXPECT_EQ(txs[1].r, 0x2cfaa5ffa42172bfa9f83207a257c53ba3a106844ee58e9131466f655ecc11e9_u256);
    EXPECT_EQ(txs[1].s, 0x419366dadd905a16cd433f2953f9ed976560822bb2611ac192b939f7b9c2a98c_u256);
    EXPECT_EQ(txs[1].v, 1);
    EXPECT_EQ(txs[1].chain_id, 1);
}

TEST(state_rlp, decode_invalid_transaction)
{
    {
        const auto input =
            "05f8e4013e8503a4dec79482c835949232a548dd9e81bac65500b5e0d918f8ba93675c80b844095ea7b300"
            "00"
            "00000000000000000000f17d23136b4fead139f54fb766c8795faae09660ffffffffffffffffffffffffff"
            "ffff"
            "fffffffffffffffffffffffffffffffffff838f7949232a548dd9e81bac65500b5e0d918f8ba93675ce1a0"
            "8e94"
            "7fe742892ee6fffe7cfc013acac35d33a3892c58597344bed88b21eb1d2f01a02cfaa5ffa42172bfa9f832"
            "07a2"
            "57c53ba3a106844ee58e9131466f655ecc11e9a0419366dadd905a16cd433f2953f9ed976560822bb2611a"
            "c192"
            "b939f7b9c2a98c";

        EXPECT_THAT([&] { decode_helper<state::Transaction>(input); },
            ThrowsMessage<std::runtime_error>("rlp decoding error: unexpected transaction type."));
    }
    {
        const auto input =
            "01b8e4013e8503a4dec79482c835949232a548dd9e81bac65500b5e0d918f8ba93675c80b844095ea7b300"
            "00"
            "00000000000000000000f17d23136b4fead139f54fb766c8795faae09660ffffffffffffffffffffffffff"
            "ffff"
            "fffffffffffffffffffffffffffffffffff838f7949232a548dd9e81bac65500b5e0d918f8ba93675ce1a0"
            "8e94"
            "7fe742892ee6fffe7cfc013acac35d33a3892c58597344bed88b21eb1d2f01a02cfaa5ffa42172bfa9f832"
            "07a2"
            "57c53ba3a106844ee58e9131466f655ecc11e9a0419366dadd905a16cd433f2953f9ed976560822bb2611a"
            "c192"
            "b939f7b9c2a98c";

        EXPECT_THAT([&] { decode_helper<state::Transaction>(input); },
            ThrowsMessage<std::runtime_error>(
                "rlp decoding error: unexpected type. list expected"));
    }
}
