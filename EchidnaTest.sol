// SPDX-License-Identifier: BSD-4-Clause
pragma solidity ^0.8.18;

import "ABDKMath64x64.sol";

int128 constant MIN_64x64 = -0x80000000000000000000000000000000;

int128 constant MAX_64x64 = 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

function between(uint256 val, uint256 lower, uint256 upper) pure returns (uint256) {
    return lower + (val % (upper - lower + 1));
}

contract Test {
    int128 internal zero = ABDKMath64x64.fromInt(0);
    int128 internal one = ABDKMath64x64.fromInt(1);

    event Value(string, int64);

    /**
     *                    _       ___
     *    _              | |     / __)
     *  _| |_ ___       / /    _| |__ ____ ___  ____
     * (_   _) _ \     / /    (_   __) ___) _ \|    \
     *   | || |_| |   / /       | | | |  | |_| | | | |
     *    \__)___/   |_|        |_| |_|   \___/|_|_|_|
     */

    // assert fromUInt gets back from toUInt
    function fromUInt_toUInt(uint128 x) public {
        int128 x64 = ABDKMath64x64.fromUInt(x);
        uint256 result = ABDKMath64x64.toUInt(x64);
        assert(result == x);
    }

    // assert fromInt gets back from toInt
    function fromInt_toInt(int256 x) public {
        int128 x64 = ABDKMath64x64.fromInt(x);
        int256 result = ABDKMath64x64.toInt(x64);
        assert(result == x);
    }

    // asssert from128x128 gets back from to128x128
    function from128x128_to128x128(int128 x) public {
        x = ABDKMath64x64.fromInt(x);
        int256 x128 = ABDKMath64x64.to128x128(x);
        assert(ABDKMath64x64.from128x128(x128) == x);
    }

    function debug(string memory x, int128 y) public {
        emit Value(x, ABDKMath64x64.toInt(y));
    }

    /**
     *                _     _
     *               | |   | |
     *      _____  __| | __| |
     *     (____ |/ _  |/ _  |
     *     / ___ ( (_| ( (_| |
     *     \_____|\____|\____|
     */

    // test commutative property of add
    function add_commutative(int128 x, int128 y) public {
        (x, y) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y));
        assert(ABDKMath64x64.add(y, x) == ABDKMath64x64.add(x, y));
    }

    // test associative property of add
    function add_associative(int128 x, int128 y, int128 z) public {
        (x, y, z) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y), ABDKMath64x64.fromInt(z));
        assert(ABDKMath64x64.add(x, ABDKMath64x64.add(y, z)) == ABDKMath64x64.add(ABDKMath64x64.add(x, y), z));
    }

    // test identity element - add
    function identity_element_add(int128 x) public {
        (x) = (ABDKMath64x64.fromInt(x));
        assert(ABDKMath64x64.add(x, zero) == x);
    }

    // test inverse element - add
    function inverse_element_add(int128 x) public {
        (x) = (ABDKMath64x64.fromInt(x));
        assert(ABDKMath64x64.add(x, ABDKMath64x64.neg(x)) == zero);
    }

    // assert result is gte both inputs when dealing with uints
    function add_uints_uponly(uint128 x, uint128 y) public returns (int128 result) {
        (int128 x64, int128 y64) = (ABDKMath64x64.fromUInt(x), ABDKMath64x64.fromUInt(y));
        result = ABDKMath64x64.add(x64, y64);
        assert(result >= x64 && result >= y64);
    }

    // assert sum minus x gets back to y
    function add_then_sub(int128 x, int128 y) public returns (int128) {
        (x, y) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y));
        int128 result = ABDKMath64x64.add(x, y);
        assert(ABDKMath64x64.sub(result, y) == x);
    }

    /**
     *         _
     *        | |
     *   ___ _   _| |__
     *  /___) | | |  _ \
     * |___ | |_| | |_) )
     * (___/|____/|____/
     */

    // test sub is inverse of add
    function sub_is_inverse_of_add(int128 x, int128 y) public {
        (x, y) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y));
        assert(ABDKMath64x64.sub(ABDKMath64x64.add(x, y), y) == x);
    }

    // test sub is add with neg
    function sub_is_add_with_neg(int128 x, int128 y) public {
        (x, y) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y));
        assert(ABDKMath64x64.sub(x, y) == ABDKMath64x64.add(x, ABDKMath64x64.neg(y)));
    }

    // test sub with uints is downonly for x
    function sub_uints_downonly(uint128 x, uint128 y) public returns (int128 result) {
        (int128 x64, int128 y64) = (ABDKMath64x64.fromUInt(x), ABDKMath64x64.fromUInt(y));
        result = ABDKMath64x64.sub(x64, y64);
        assert(result <= x64);
    }

    // test sub identity element
    function sub_identity_element(int128 x) public {
        (x) = (ABDKMath64x64.fromInt(x));
        assert(ABDKMath64x64.sub(x, zero) == x);
    }

    /**
     *                _
     *               | |
     *    ____  _   _| |
     *   |    \| | | | |
     *   | | | | |_| | |
     *   |_|_|_|____/ \_)
     */

    // test commutative property of mul
    function mul_commutative(int128 x, int128 y) public {
        (x, y) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y));
        assert(ABDKMath64x64.mul(y, x) == ABDKMath64x64.mul(x, y));
    }

    // test associative property of mul
    function mul_associative(int128 x, int128 y, int128 z) public {
        (x, y, z) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y), ABDKMath64x64.fromInt(z));
        assert(ABDKMath64x64.mul(x, ABDKMath64x64.mul(y, z)) == ABDKMath64x64.mul(ABDKMath64x64.mul(x, y), z));
    }

    // test distributive property of mul over add
    function mul_distributive(int128 x, int128 y, int128 z) public {
        (x, y, z) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y), ABDKMath64x64.fromInt(z));
        assert(
            ABDKMath64x64.mul(x, ABDKMath64x64.add(y, z))
                == ABDKMath64x64.add(ABDKMath64x64.mul(x, y), ABDKMath64x64.mul(x, z))
        );
    }

    // test distributive property of mul over sub
    function mul_distributive_sub(int128 x, int128 y, int128 z) public {
        (x, y, z) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y), ABDKMath64x64.fromInt(z));
        assert(
            ABDKMath64x64.mul(x, ABDKMath64x64.sub(y, z))
                == ABDKMath64x64.sub(ABDKMath64x64.mul(x, y), ABDKMath64x64.mul(x, z))
        );
    }

    // test identity element - mul
    function identity_element_mul(int128 x) public {
        (x) = (ABDKMath64x64.fromInt(x));
        assert(ABDKMath64x64.mul(x, one) == x);
    }

    // test inverse element - mul  NOTE: COULD NOT GET THIS TO WORK
    // function inverse_element_mul(int128 x) public {
    //     (x) = (ABDKMath64x64.fromInt(x));
    //     int128 inv_ = ABDKMath64x64.inv(x);
    //     require(inv_ != 0);
    //     require(inv_ != zero);
    //     int128 result = ABDKMath64x64.mul(x, inv_);
    //     debug("x", x);
    //     debug("inv", inv_);
    //     debug("result", result);
    //     assert( result == one);
    //     // assert(ABDKMath64x64.mul(x, ABDKMath64x64.inv(x)) == one);
    // }

    // assert product divide by x gets back to y
    function mul_then_div(int128 x, int128 y) public returns (int128) {
        (x, y) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y));
        int128 result = ABDKMath64x64.mul(x, y);
        assert(ABDKMath64x64.div(result, y) == x);
    }

    /**
     *                 _  _
     *                | |(_)
     *     ____  _   _| | _
     *    |    \| | | | || |
     *    | | | | |_| | || |
     *    |_|_|_|____/ \_)_|
     */

    // test commutative property of muli
    function muli_commutative(int128 x, int256 y) public {
        int128 x64 = ABDKMath64x64.fromInt(x);
        x = ABDKMath64x64.toInt(x64);
        int128 y64 = ABDKMath64x64.fromInt(y);
        y = ABDKMath64x64.toInt(y64);
        assert(ABDKMath64x64.muli(x64, y) == ABDKMath64x64.muli(y64, x));
    }

    // test associative property of muli
    function muli_associative(int128 x, int128 y, int256 z) public {
        (x, y) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y));
        int256 result1 = ABDKMath64x64.muli(x, ABDKMath64x64.muli(y, z));
        int256 result2 = ABDKMath64x64.muli(ABDKMath64x64.fromInt(ABDKMath64x64.muli(x, ABDKMath64x64.toInt(y))), z);
        assert(result1 == result2);
    }

    // test distributive property of muli over add
    function muli_distributive(int128 x, int128 y, int128 z) public {
        (int128 x64, int128 y64, int128 z64) =
            (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y), ABDKMath64x64.fromInt(z));
        (x, y, z) = (ABDKMath64x64.toInt(x64), ABDKMath64x64.toInt(y64), ABDKMath64x64.toInt(z64));
        int128 result1 = ABDKMath64x64.fromInt(ABDKMath64x64.muli(x, ABDKMath64x64.add(y64, z64)));
        int128 result2 = ABDKMath64x64.add(
            ABDKMath64x64.fromInt(ABDKMath64x64.muli(x64, y)), ABDKMath64x64.fromInt(ABDKMath64x64.muli(x64, z))
        );
        assert(result1 == result2);
    }

    // test distributive property of muli over sub
    function muli_distributive_sub(int128 x, int128 y, int128 z) public {
        (int128 x64, int128 y64, int128 z64) =
            (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y), ABDKMath64x64.fromInt(z));
        (x, y, z) = (ABDKMath64x64.toInt(x64), ABDKMath64x64.toInt(y64), ABDKMath64x64.toInt(z64));
        int128 result1 = ABDKMath64x64.fromInt(ABDKMath64x64.muli(x, ABDKMath64x64.sub(y64, z64)));
        int128 result2 = ABDKMath64x64.sub(
            ABDKMath64x64.fromInt(ABDKMath64x64.muli(x64, y)), ABDKMath64x64.fromInt(ABDKMath64x64.muli(x64, z))
        );
        assert(result1 == result2);
    }

    // test identity element - muli
    function identity_element_muli(int128 x) public {
        (int128 x64) = (ABDKMath64x64.fromInt(x));
        assert(ABDKMath64x64.muli(x64, int256(1)) == ABDKMath64x64.toInt(x64));
    }

    // assert product divide by x gets back to y
    function muli_then_div(int128 x, int128 y) public {
        (int128 x64, int128 y64) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y));
        (x, y) = (ABDKMath64x64.toInt(x64), ABDKMath64x64.toInt(y64));
        int256 result = ABDKMath64x64.muli(x64, y);
        assert(ABDKMath64x64.div(ABDKMath64x64.fromInt(result), y64) == x64);
    }

    /**
     *                _
     *               | |
     *    ____  _   _| | _   _
     *   |    \| | | | || | | |
     *   | | | | |_| | || |_| |
     *   |_|_|_|____/ \_)____/
     */
    // test commutative property of mulu
    function mulu_commutative(int128 x, uint256 y) public {
        int128 x64 = ABDKMath64x64.fromInt(x);
        uint256 x_Uint = ABDKMath64x64.toUInt(x64);
        int128 y64 = ABDKMath64x64.fromUInt(y);
        assert(ABDKMath64x64.mulu(x64, y) == ABDKMath64x64.mulu(y64, x_Uint));
    }

    // test associative property of mulu
    function mulu_associative(int128 x, int128 y, uint256 z) public {
        (x, y) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y));
        uint256 result1 = ABDKMath64x64.mulu(x, ABDKMath64x64.mulu(y, z));
        uint256 result2 = ABDKMath64x64.mulu(ABDKMath64x64.fromUInt(ABDKMath64x64.mulu(x, ABDKMath64x64.toUInt(y))), z);
        assert(result1 == result2);
    }

    // test distributive property of mulu over add
    function mulu_distributive(uint128 x, uint128 y, uint128 z) public {
        (int128 x64, int128 y64, int128 z64) =
            (ABDKMath64x64.fromUInt(x), ABDKMath64x64.fromUInt(y), ABDKMath64x64.fromUInt(z));
        int128 result1 =
            ABDKMath64x64.fromUInt(ABDKMath64x64.mulu(x64, ABDKMath64x64.toUInt(ABDKMath64x64.add(y64, z64))));
        int128 result2 = ABDKMath64x64.add(
            ABDKMath64x64.fromUInt(ABDKMath64x64.mulu(x64, y)), ABDKMath64x64.fromUInt(ABDKMath64x64.mulu(x64, z))
        );
        assert(result1 == result2);
    }

    // test distributive property of mulu over sub
    function mulu_distributive_sub(uint128 x, uint128 y, uint128 z) public {
        (int128 x64, int128 y64, int128 z64) =
            (ABDKMath64x64.fromUInt(x), ABDKMath64x64.fromUInt(y), ABDKMath64x64.fromUInt(z));
        int128 result1 =
            ABDKMath64x64.fromUInt(ABDKMath64x64.mulu(x64, ABDKMath64x64.toUInt(ABDKMath64x64.sub(y64, z64))));
        int128 result2 = ABDKMath64x64.sub(
            ABDKMath64x64.fromUInt(ABDKMath64x64.mulu(x64, y)), ABDKMath64x64.fromUInt(ABDKMath64x64.mulu(x64, z))
        );
        assert(result1 == result2);
    }

    // test identity element - mulu
    function identity_element_mulu(int128 x) public {
        (int128 x64) = (ABDKMath64x64.fromInt(x));
        assert(ABDKMath64x64.mulu(x64, uint256(1)) == ABDKMath64x64.toUInt(x64));
    }

    // assert product divide by x gets back to y
    function mulu_then_div(int128 x, uint128 y) public {
        (int128 x64, int128 y64) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromUInt(y));
        uint256 result = ABDKMath64x64.mulu(x64, y);
        assert(ABDKMath64x64.div(ABDKMath64x64.fromUInt(result), y64) == x64);
    }

    /**
     *      _ _
     *     | (_)
     *   __| |_ _   _
     *  / _  | | | | |
     * ( (_| | |\ V /
     *  \____|_| \_/
     */

    // test div (x + y) / z == x/z + y/z
    function div_add(int128 x, int128 y, int128 z) public {
        require(z != 0);
        (int128 x64, int128 y64, int128 z64) =
            (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y), ABDKMath64x64.fromInt(z));
        int128 result1 = ABDKMath64x64.div(ABDKMath64x64.add(x64, y64), z64);
        int128 result2 = ABDKMath64x64.add(ABDKMath64x64.div(x64, z64), ABDKMath64x64.div(y64, z64));
        assert(ABDKMath64x64.toInt(result1) == ABDKMath64x64.toInt(result2));
    }

    // test div x / y back to x using mul
    function div_then_mul(int128 x, int128 y) public {
        require(y != 0);
        (int128 x64, int128 y64) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y));
        require(x64 > y64);
        int128 result = ABDKMath64x64.div(x64, y64);
        assert(ABDKMath64x64.fromInt(ABDKMath64x64.mul(result, y64)) == x);
    }

    // no tests for DIVI / DIVU

    /**
     *     ____  _____  ____
     *    |  _ \| ___ |/ _  |
     *    | | | | ____( (_| |
     *    |_| |_|_____)\___ |
     *                (_____|
     */
    // test neg w two's complement
    function neg_twos_complement(int128 x) public {
        (x) = (ABDKMath64x64.fromInt(x));
        assert(ABDKMath64x64.neg(x) == (~x + 1));
    }

    // test neg using subtract
    function neg_sub(int128 x) public {
        (x) = (ABDKMath64x64.fromInt(x));
        assert(ABDKMath64x64.neg(x) == (ABDKMath64x64.sub(zero, x)));
    }

    /**
     *            _
     *           | |
     *      _____| |__   ___
     *     (____ |  _ \ /___)
     *     / ___ | |_) )___ |
     *     \_____|____/(___/
     */

    // test assert abs always >= 0
    function abs_positive(int128 x) public {
        (x) = (ABDKMath64x64.fromInt(x));
        assert(ABDKMath64x64.abs(x) >= zero);
    }

    // test if x < 0 then abs(x) == neg(x)
    function abs_neg(int128 x) public {
        (x) = (ABDKMath64x64.fromInt(x));
        if (x < zero) {
            assert(ABDKMath64x64.abs(x) == ABDKMath64x64.neg(x));
        }
    }

    // test if sign is same then abs(x*y) == x*y
    function abs_mul(int128 x, int128 y) public {
        (x, y) = (ABDKMath64x64.fromInt(x), ABDKMath64x64.fromInt(y));
        require((x > 0 && y > 0) || (x < 0 && y < 0));
        assert(ABDKMath64x64.abs(ABDKMath64x64.mul(x, y)) == ABDKMath64x64.mul(x, y));
    }

    /**
     *       _
     *      (_)
     *       _ ____ _   _
     *      | |  _ \ | | |
     *      | | | | \ V /
     *      |_|_| |_|\_/
     */


    // test inv is 1 / x
    function inv(int128 x) public {
        (x) = (ABDKMath64x64.fromInt(x));
        require(x != 0);
        assert(ABDKMath64x64.inv(x) == ABDKMath64x64.div(one, x));
    }

    // test inv of 1/x is x
    function inv_inv(int128 x) public {
        (x) = (ABDKMath64x64.fromInt(x));
        require(x != 0);
        assert(ABDKMath64x64.inv(ABDKMath64x64.inv(x)) == x);
    }

    // test abs(inv(x)) is always smaller than abs(x)
    function inv_abs(int128 x) public {
        (x) = (ABDKMath64x64.fromInt(x));
        require(x != 0);
        assert(ABDKMath64x64.abs(ABDKMath64x64.inv(x)) < ABDKMath64x64.abs(x));
    }

    /**
     *       _____ _   _ ____
     *      (____ | | | / _  |
     *      / ___ |\ V ( (_| |
     *      \_____| \_/ \___ |
     *                 (_____|
     */


    /**
     *        ____ _____ _   _ ____
     *       / _  (____ | | | / _  |
     *      ( (_| / ___ |\ V ( (_| |
     *       \___ \_____| \_/ \___ |
     *      (_____|          (_____|
     */

    /**
     *       ____   ___  _ _ _
     *      |  _ \ / _ \| | | |
     *      | |_| | |_| | | | |
     *      |  __/ \___/ \___/
     *      |_|
     */
    /**
     *                          _
     *        ___  ____  ____ _| |_
     *       /___)/ _  |/ ___|_   _)
     *      |___ | |_| | |     | |_
     *      (___/ \__  |_|      \__)
     *               |_|
     */
    /**
     *       _                     ______
     *      | |                   (_____ \
     *      | | ___   ____          ____) )
     *      | |/ _ \ / _  |        / ____/
     *      | | |_| ( (_| |_______| (_____
     *       \_)___/ \___ (_______)_______)
     *              (_____|
     */
    /**
     *      _
     *      | |
     *      | | ____
     *      | ||  _ \
     *      | || | | |
     *       \_)_| |_|
     */
    /**
     *                                ______
     *                               (_____ \
     *       _____ _   _ ____          ____) )
     *      | ___ ( \ / )  _ \        / ____/
     *      | ____|) X (| |_| |______| (_____
     *      |_____|_/ \_)  __(_______)_______)
     *                  |_|
     */
    /**
     *      _____ _   _ ____
     *      | ___ ( \ / )  _ \
     *      | ____|) X (| |_| |
     *      |_____|_/ \_)  __/
     *                  |_|
     */
    /**
     *           _ _
     *          | (_)
     *        __| |_ _   _ _   _ _   _
     *       / _  | | | | | | | | | | |
     *      ( (_| | |\ V /| |_| | |_| |
     *       \____|_| \_/ |____/|____/
     */
    /**
     *                          _
     *        ___  ____  ____ _| |_ _   _
     *       /___)/ _  |/ ___|_   _) | | |
     *      |___ | |_| | |     | |_| |_| |
     *      (___/ \__  |_|      \__)____/
     *               |_|
     */
}
