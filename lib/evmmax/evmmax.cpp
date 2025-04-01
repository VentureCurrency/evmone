// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2023 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <evmmax/evmmax.hpp>

using namespace intx;

namespace evmmax
{
struct EXMMAXModStateInterface
{
    [[nodiscard]] virtual bool loadx(
        uint8_t* out_ptr, size_t val_idx, size_t num_vals) const noexcept = 0;
    [[nodiscard]] virtual bool storex(
        const uint8_t* in_ptr, size_t dst_val_idx, size_t num_vals) noexcept = 0;
    [[nodiscard]] virtual bool addmodx(size_t dst_idx, size_t dst_stride, size_t x_idx,
        size_t x_stride, size_t y_idx, size_t y_stride, size_t count) noexcept = 0;
    [[nodiscard]] virtual bool submodx(size_t dst_idx, size_t dst_stride, size_t x_idx,
        size_t x_stride, size_t y_idx, size_t y_stride, size_t count) noexcept = 0;
    [[nodiscard]] virtual bool mulmodx(size_t dst_idx, size_t dst_stride, size_t x_idx,
        size_t x_stride, size_t y_idx, size_t y_stride, size_t count) noexcept = 0;
    virtual void print(std::ostream& out) noexcept = 0;

    [[nodiscard]] virtual size_t value_size() const noexcept = 0;
    [[nodiscard]] virtual size_t num_values() const noexcept = 0;

    virtual ~EXMMAXModStateInterface() noexcept = default;
};

namespace
{
/// Copy of intx::be::unsafe::load but with additional src size parameter
template <typename IntT>
inline IntT load(const uint8_t* src, size_t src_size) noexcept
{
    // Align bytes.
    // TODO: Using memcpy() directly triggers this optimization bug in GCC:
    //   https://gcc.gnu.org/bugzilla/show_bug.cgi?id=107837
    alignas(IntT) std::byte aligned_storage[sizeof(IntT)] = {};
    std::memcpy(&aligned_storage[sizeof(IntT) - src_size], src, src_size);
    // TODO(C++23): Use std::start_lifetime_as<uint256>().
    return to_big_endian(*reinterpret_cast<const IntT*>(&aligned_storage));
}

template <typename T>
inline void store(uint8_t* dst, const T& x, size_t dst_size) noexcept
{
    const auto d = to_big_endian(x);
    std::memcpy(dst, &reinterpret_cast<const std::byte*>(&d)[sizeof(T) - dst_size], dst_size);
}

template <typename UintT>
struct EXMMAXModState : public EXMMAXModStateInterface
{
    std::vector<UintT> values;
    const ModArith<UintT> arith;
    const size_t value_size_in_bytes;

    explicit EXMMAXModState(const UintT& _mod, size_t mod_size, size_t vals_used) noexcept
      : arith(_mod), value_size_in_bytes((mod_size + 7) / 8)
    {
        values.resize(vals_used);
    }

    [[nodiscard]] bool loadx(
        uint8_t* out_ptr, size_t val_idx, size_t num_vals) const noexcept override
    {
        if (!(val_idx + num_vals <= values.size()))
            return false;

        for (unsigned i = 0; i < num_vals; ++i)
        {
            store(out_ptr + i * value_size_in_bytes, arith.from_mont(values[val_idx + i]),
                value_size_in_bytes);
        }

        return true;
    }

    [[nodiscard]] bool storex(
        const uint8_t* in_ptr, size_t dst_val_idx, size_t num_vals) noexcept override
    {
        if (!(dst_val_idx + num_vals <= values.size()))
            return false;

        for (unsigned i = 0; i < num_vals; ++i)
        {
            values[dst_val_idx + i] =
                arith.to_mont(load<UintT>(in_ptr + value_size_in_bytes * i, value_size_in_bytes));
        }

        return true;
    }

    [[nodiscard]] bool operation(std::function<UintT(UintT, UintT)> op, size_t dst_idx,
        size_t dst_stride, size_t x_idx, size_t x_stride, size_t y_idx, size_t y_stride,
        size_t count) noexcept
    {
        if (std::max(dst_idx + dst_stride * (count - 1),
                std::max(x_idx + x_stride * (count - 1), y_idx + y_stride * (count - 1))) >=
            values.size())
            return false;

        for (size_t i = 0; i < count; ++i)
            values[dst_idx + i * dst_stride] =
                op(values[x_idx + i * x_stride], values[y_idx + i * y_stride]);

        return true;
    }

    [[nodiscard]] bool addmodx(size_t dst_idx, size_t dst_stride, size_t x_idx, size_t x_stride,
        size_t y_idx, size_t y_stride, size_t count) noexcept override
    {
        return operation([&](const UintT& x, const UintT& y) { return arith.add(x, y); }, dst_idx,
            dst_stride, x_idx, x_stride, y_idx, y_stride, count);
    }

    [[nodiscard]] bool submodx(size_t dst_idx, size_t dst_stride, size_t x_idx, size_t x_stride,
        size_t y_idx, size_t y_stride, size_t count) noexcept override
    {
        return operation([&](const UintT& x, const UintT& y) { return arith.sub(x, y); }, dst_idx,
            dst_stride, x_idx, x_stride, y_idx, y_stride, count);
    }

    [[nodiscard]] bool mulmodx(size_t dst_idx, size_t dst_stride, size_t x_idx, size_t x_stride,
        size_t y_idx, size_t y_stride, size_t count) noexcept override
    {
        return operation([&](const UintT& x, const UintT& y) { return arith.mul(x, y); }, dst_idx,
            dst_stride, x_idx, x_stride, y_idx, y_stride, count);
    }

    void print(std::ostream& out) noexcept override
    {
        out << "{ \n";
        for (size_t i = 0; i < values.size(); ++i)
        {
            if (values[i] != 0)
                out << "\t" << i << ": " << size_t(arith.from_mont(values[i])) << ", \n";
        }
        out << "}\n";
    }

    [[nodiscard]] size_t num_values() const noexcept override { return values.size(); }
    [[nodiscard]] size_t value_size() const noexcept override { return value_size_in_bytes; }
};

template <typename UintT>
struct EXMMAXModStateSmallValues : public EXMMAXModStateInterface
{
    std::vector<UintT> values;
    const size_t value_size_in_bytes;
    const UintT mod;

    explicit EXMMAXModStateSmallValues(
        const UintT& _mod, size_t mod_size, size_t vals_used) noexcept
      : value_size_in_bytes((mod_size + 7) / 8), mod(_mod)
    {
        values.resize(vals_used);
    }

    [[nodiscard]] bool loadx(
        uint8_t* out_ptr, size_t val_idx, size_t num_vals) const noexcept override
    {
        if (!(val_idx + num_vals <= values.size()))
            return false;

        for (unsigned i = 0; i < num_vals; ++i)
            store(out_ptr + i * value_size_in_bytes, values[val_idx + i], value_size_in_bytes);

        return true;
    }

    [[nodiscard]] bool storex(
        const uint8_t* in_ptr, size_t dst_val_idx, size_t num_vals) noexcept override
    {
        if (!(dst_val_idx + num_vals <= values.size()))
            return false;

        for (unsigned i = 0; i < num_vals; ++i)
        {
            values[dst_val_idx + i] =
                load<UintT>(in_ptr + value_size_in_bytes * i, value_size_in_bytes) % mod;
        }

        return true;
    }

    [[nodiscard]] bool addmodx(size_t dst_idx, size_t dst_stride, size_t x_idx, size_t x_stride,
        size_t y_idx, size_t y_stride, size_t count) noexcept override
    {
        //        if (std::max(dst_idx + dst_stride * (count - 1),
        //                std::max(x_idx + x_stride * (count - 1), y_idx + y_stride * (count - 1)))
        //                >=
        //            values.size())
        //            return false;

        for (size_t i = 0; i < count; ++i)
        {
            values[dst_idx + i * dst_stride] =
                values[x_idx + i * x_stride] + values[y_idx + i * y_stride];

            values[dst_idx + i * dst_stride] %= mod;
        }

        return true;
    }

    [[nodiscard]] bool submodx(size_t dst_idx, size_t dst_stride, size_t x_idx, size_t x_stride,
        size_t y_idx, size_t y_stride, size_t count) noexcept override
    {
        //        if (std::max(dst_idx + dst_stride * (count - 1),
        //                std::max(x_idx + x_stride * (count - 1), y_idx + y_stride * (count - 1)))
        //                >=
        //            values.size())
        //            return false;

        for (size_t i = 0; i < count; ++i)
        {
            values[dst_idx + i * dst_stride] =
                values[y_idx + i * y_stride] > values[x_idx + i * x_stride] ?
                    values[x_idx + i * x_stride] + mod - values[y_idx + i * y_stride] :
                    values[x_idx + i * x_stride] - values[y_idx + i * y_stride];
        }

        return true;
    }

    [[nodiscard]] bool mulmodx(size_t dst_idx, size_t dst_stride, size_t x_idx, size_t x_stride,
        size_t y_idx, size_t y_stride, size_t count) noexcept override
    {
        //        if (std::max(dst_idx + dst_stride * (count - 1),
        //                std::max(x_idx + x_stride * (count - 1), y_idx + y_stride * (count - 1)))
        //                >=
        //            values.size())
        //            return false;

        for (size_t i = 0; i < count; ++i)
        {
            values[dst_idx + i * dst_stride] =
                values[x_idx + i * x_stride] * values[y_idx + i * y_stride];

            values[dst_idx + i * dst_stride] %= mod;
        }

        return true;
    }

    void print(std::ostream& out) noexcept override
    {
        out << "{ \n";
        for (size_t i = 0; i < values.size(); ++i)
        {
            if (values[i] != 0)
                out << "\t" << i << ": " << size_t(values[i]) << ", \n";
        }
        out << "}\n";
    }

    [[nodiscard]] size_t num_values() const noexcept override { return values.size(); }
    [[nodiscard]] size_t value_size() const noexcept override { return value_size_in_bytes; }
};

[[nodiscard]] std::unique_ptr<EXMMAXModStateInterface> create_mod_state(
    const uint8_t* mod_ptr, size_t mod_size, size_t vals_used) noexcept
{
    // Must be odd.
    const auto mod_size_bytes = (mod_size + 7) / 8;
    assert((mod_ptr[mod_size_bytes - 1] & 1) == 1);
    // Max mod size must be <= 4096 bits
    assert(mod_size_bytes <= 512);

    // We make the registers 2 times bigger to avoid using additional memory to handle overflows.
    // For small values only
    if (mod_size_bytes <= 2)
    {
        return std::make_unique<EXMMAXModStateSmallValues<uint32_t>>(
            load<uint32_t>(mod_ptr, mod_size_bytes), mod_size, vals_used);
    }
    if (mod_size_bytes <= 4)
    {
        return std::make_unique<EXMMAXModStateSmallValues<uint64_t>>(
            load<uint64_t>(mod_ptr, mod_size_bytes), mod_size, vals_used);
    }
    if (mod_size_bytes <= 16)
    {
        return std::make_unique<EXMMAXModState<intx::uint128>>(
            load<intx::uint128>(mod_ptr, mod_size_bytes), mod_size, vals_used);
    }
    else if (mod_size_bytes <= 32)
    {
        return std::make_unique<EXMMAXModState<uint256>>(
            load<uint256>(mod_ptr, mod_size_bytes), mod_size, vals_used);
    }
    else if (mod_size_bytes <= 48)
    {
        return std::make_unique<EXMMAXModState<uint384>>(
            load<uint384>(mod_ptr, mod_size_bytes), mod_size, vals_used);
    }
    else
        return nullptr;
}

[[nodiscard]] bool charge_gas_precompute_mont(int64_t& gas_left, size_t mod_size) noexcept
{
    // TODO: Set proper values for A and B
    static constexpr int64_t A = 1;
    static constexpr int64_t B = 5;

    const size_t val_size_multiplier = (mod_size + 7) / (8 * 8);

    if (val_size_multiplier < 50)
        gas_left -= A * static_cast<int64_t>(val_size_multiplier) + B;
    else
    {
        // TODO: Add support for subquadratic mulmont cost model
        assert(false);
        return false;
    }

    return gas_left >= 0;
}

[[nodiscard]] bool validate_memory_usage(size_t val_size, size_t num_val) noexcept
{
    static constexpr auto EVMMAX_MAX_MEM_SIZE = 65536;

    return val_size * num_val <= EVMMAX_MAX_MEM_SIZE;
}

}  // namespace

[[nodiscard]] bool EVMMAXState::is_activated() const noexcept
{
    return active_mod != nullptr;
}

[[nodiscard]] evmc_status_code EVMMAXState::setmodx(
    int64_t& gas_left, const uint8_t* mod_ptr, size_t mod_size, size_t alloc_count) noexcept
{
    if (!validate_memory_usage((mod_size + 7) / 8, alloc_count))
        return EVMC_FAILURE;

    if (!charge_gas_precompute_mont(gas_left, mod_size))
        return EVMC_OUT_OF_GAS;

    active_mod = create_mod_state(mod_ptr, mod_size, alloc_count);
    if (active_mod != nullptr)
    {
        if (mod_size <= 192)
        {
            current_gas_cost = {
                .addmodx = 1,
                .mulmodx = 1,
            };
        }
        else if (mod_size <= 320)
        {
            current_gas_cost = {
                .addmodx = 1,
                .mulmodx = 2,
            };
        }
        else if (mod_size <= 384)
        {
            current_gas_cost = {
                .addmodx = 1,
                .mulmodx = 3,
            };
        }
        else
        {
            assert(false);
            return EVMC_FAILURE;
        }


        return EVMC_SUCCESS;
    }
    else
        return EVMC_FAILURE;
}

[[nodiscard]] evmc_status_code EVMMAXState::loadx(
    int64_t& gas_left, uint8_t* out_ptr, size_t val_idx, size_t num_vals) noexcept
{
    if (!is_activated())
        return EVMC_FAILURE;

    if ((gas_left -= current_gas_cost.mulmodx * static_cast<int64_t>(num_vals)) < 0)
        return EVMC_OUT_OF_GAS;

    return active_mod->loadx(out_ptr, val_idx, num_vals) ? EVMC_SUCCESS : EVMC_FAILURE;
}

[[nodiscard]] evmc_status_code EVMMAXState::storex(
    int64_t& gas_left, const uint8_t* in_ptr, size_t dst_val_idx, size_t num_vals) noexcept
{
    if (!is_activated())
        return EVMC_FAILURE;

    if ((gas_left -= current_gas_cost.mulmodx * static_cast<int64_t>(num_vals)) < 0)
        return EVMC_OUT_OF_GAS;

    return active_mod->storex(in_ptr, dst_val_idx, num_vals) ? EVMC_SUCCESS : EVMC_FAILURE;
}

[[nodiscard]] evmc_status_code EVMMAXState::addmodx(int64_t& gas_left, size_t dst_idx,
    size_t dst_stride, size_t x_idx, size_t x_stride, size_t y_idx, size_t y_stride,
    size_t count) noexcept
{
    if (!is_activated())
        return EVMC_FAILURE;

    if ((gas_left -= current_gas_cost.addmodx * static_cast<int64_t>(count)) < 0)
        return EVMC_OUT_OF_GAS;

    return active_mod->addmodx(dst_idx, dst_stride, x_idx, x_stride, y_idx, y_stride, count) ?
               EVMC_SUCCESS :
               EVMC_FAILURE;
}

[[nodiscard]] evmc_status_code EVMMAXState::submodx(int64_t& gas_left, size_t dst_idx,
    size_t dst_stride, size_t x_idx, size_t x_stride, size_t y_idx, size_t y_stride,
    size_t count) noexcept
{
    if (!is_activated())
        return EVMC_FAILURE;

    if ((gas_left -= current_gas_cost.addmodx * static_cast<int64_t>(count)) < 0)
        return EVMC_OUT_OF_GAS;

    return active_mod->submodx(dst_idx, dst_stride, x_idx, x_stride, y_idx, y_stride, count) ?
               EVMC_SUCCESS :
               EVMC_FAILURE;
}

[[nodiscard]] evmc_status_code EVMMAXState::mulmodx(int64_t& gas_left, size_t dst_idx,
    size_t dst_stride, size_t x_idx, size_t x_stride, size_t y_idx, size_t y_stride,
    size_t count) noexcept
{
    if (!is_activated())
        return EVMC_FAILURE;

    if ((gas_left -= current_gas_cost.mulmodx * static_cast<int64_t>(count)) < 0)
        return EVMC_OUT_OF_GAS;

    return active_mod->mulmodx(dst_idx, dst_stride, x_idx, x_stride, y_idx, y_stride, count) ?
               EVMC_SUCCESS :
               EVMC_FAILURE;
}

[[nodiscard]] size_t EVMMAXState::active_mod_value_size() const noexcept
{
    if (!is_activated())
        return 0;

    return active_mod->value_size();
}

void EVMMAXState::print_state(std::ostream& out) const noexcept
{
    if (!is_activated())
        return;

    active_mod->print(out);
}

void EVMMAXState::clear() noexcept
{
    active_mod = nullptr;
}

EVMMAXState& EVMMAXState::operator=(EVMMAXState&&) noexcept = default;
EVMMAXState::EVMMAXState(EVMMAXState&&) noexcept = default;
EVMMAXState::EVMMAXState() noexcept = default;
EVMMAXState::~EVMMAXState() = default;

}  // namespace evmmax
