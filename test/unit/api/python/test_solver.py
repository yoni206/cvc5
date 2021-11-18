###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Ying Sheng
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

import pytest
import pycvc5
import sys

from pycvc5 import kinds


@pytest.fixture
def solver():
    return pycvc5.Solver()


def test_recoverable_exception(solver):
    solver.setOption("produce-models", "true")
    x = solver.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x).notTerm())
    with pytest.raises(RuntimeError):
        c = solver.getValue(x)


def test_supports_floating_point(solver):
    solver.mkRoundingMode(pycvc5.RoundNearestTiesToEven)


def test_get_boolean_sort(solver):
    solver.getBooleanSort()


def test_get_integer_sort(solver):
    solver.getIntegerSort()


def test_get_null_sort(solver):
    solver.getNullSort()


def test_get_real_sort(solver):
    solver.getRealSort()


def test_get_reg_exp_sort(solver):
    solver.getRegExpSort()


def test_get_string_sort(solver):
    solver.getStringSort()


def test_get_rounding_mode_sort(solver):
    solver.getRoundingModeSort()


def test_mk_array_sort(solver):
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    realSort = solver.getRealSort()
    bvSort = solver.mkBitVectorSort(32)
    solver.mkArraySort(boolSort, boolSort)
    solver.mkArraySort(intSort, intSort)
    solver.mkArraySort(realSort, realSort)
    solver.mkArraySort(bvSort, bvSort)
    solver.mkArraySort(boolSort, intSort)
    solver.mkArraySort(realSort, bvSort)

    fpSort = solver.mkFloatingPointSort(3, 5)
    solver.mkArraySort(fpSort, fpSort)
    solver.mkArraySort(bvSort, fpSort)

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkArraySort(boolSort, boolSort)


def test_mk_bit_vector_sort(solver):
    solver.mkBitVectorSort(32)
    with pytest.raises(RuntimeError):
        solver.mkBitVectorSort(0)


def test_mk_floating_point_sort(solver):
    solver.mkFloatingPointSort(4, 8)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPointSort(0, 8)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPointSort(4, 0)


def test_mk_datatype_sort(solver):
    dtypeSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    dtypeSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    dtypeSpec.addConstructor(nil)
    solver.mkDatatypeSort(dtypeSpec)

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkDatatypeSort(dtypeSpec)

    throwsDtypeSpec = solver.mkDatatypeDecl("list")
    with pytest.raises(RuntimeError):
        solver.mkDatatypeSort(throwsDtypeSpec)


def test_mk_datatype_sorts(solver):
    slv = pycvc5.Solver()

    dtypeSpec1 = solver.mkDatatypeDecl("list1")
    cons1 = solver.mkDatatypeConstructorDecl("cons1")
    cons1.addSelector("head1", solver.getIntegerSort())
    dtypeSpec1.addConstructor(cons1)
    nil1 = solver.mkDatatypeConstructorDecl("nil1")
    dtypeSpec1.addConstructor(nil1)

    dtypeSpec2 = solver.mkDatatypeDecl("list2")
    cons2 = solver.mkDatatypeConstructorDecl("cons2")
    cons2.addSelector("head2", solver.getIntegerSort())
    dtypeSpec2.addConstructor(cons2)
    nil2 = solver.mkDatatypeConstructorDecl("nil2")
    dtypeSpec2.addConstructor(nil2)

    decls = [dtypeSpec1, dtypeSpec2]
    solver.mkDatatypeSorts(decls, set([]))

    with pytest.raises(RuntimeError):
        slv.mkDatatypeSorts(decls, set([]))

    throwsDtypeSpec = solver.mkDatatypeDecl("list")
    throwsDecls = [throwsDtypeSpec]
    with pytest.raises(RuntimeError):
        solver.mkDatatypeSorts(throwsDecls, set([]))

    # with unresolved sorts
    unresList = solver.mkUninterpretedSort("ulist")
    unresSorts = set([unresList])
    ulist = solver.mkDatatypeDecl("ulist")
    ucons = solver.mkDatatypeConstructorDecl("ucons")
    ucons.addSelector("car", unresList)
    ucons.addSelector("cdr", unresList)
    ulist.addConstructor(ucons)
    unil = solver.mkDatatypeConstructorDecl("unil")
    ulist.addConstructor(unil)
    udecls = [ulist]

    solver.mkDatatypeSorts(udecls, unresSorts)
    with pytest.raises(RuntimeError):
        slv.mkDatatypeSorts(udecls, unresSorts)


def test_mk_function_sort(solver):
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort())

    # function arguments are allowed
    solver.mkFunctionSort(funSort, solver.getIntegerSort())

    # non-first-class arguments are not allowed
    reSort = solver.getRegExpSort()
    with pytest.raises(RuntimeError):
        solver.mkFunctionSort(reSort, solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        solver.mkFunctionSort(solver.getIntegerSort(), funSort)

    solver.mkFunctionSort([solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort()],\
            solver.getIntegerSort())
    funSort2 = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort())

    # function arguments are allowed
    solver.mkFunctionSort([funSort2, solver.mkUninterpretedSort("u")],\
            solver.getIntegerSort())

    with pytest.raises(RuntimeError):
        solver.mkFunctionSort([solver.getIntegerSort(),\
                solver.mkUninterpretedSort("u")],\
                funSort2)

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        slv.mkFunctionSort(slv.mkUninterpretedSort("u"),\
                solver.getIntegerSort())
    sorts1 = [solver.getBooleanSort(),\
            slv.getIntegerSort(),\
            solver.getIntegerSort()]
    sorts2 = [slv.getBooleanSort(), slv.getIntegerSort()]
    slv.mkFunctionSort(sorts2, slv.getIntegerSort())
    with pytest.raises(RuntimeError):
        slv.mkFunctionSort(sorts1, slv.getIntegerSort())
    with pytest.raises(RuntimeError):
        slv.mkFunctionSort(sorts2, solver.getIntegerSort())


def test_mk_param_sort(solver):
    solver.mkParamSort("T")
    solver.mkParamSort("")


def test_mk_predicate_sort(solver):
    solver.mkPredicateSort([solver.getIntegerSort()])
    with pytest.raises(RuntimeError):
        solver.mkPredicateSort([])

    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
            solver.getIntegerSort())
    # functions as arguments are allowed
    solver.mkPredicateSort([solver.getIntegerSort(), funSort])

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkPredicateSort([solver.getIntegerSort()])


def test_mk_record_sort(solver):
    fields = [("b", solver.getBooleanSort()),\
              ("bv", solver.mkBitVectorSort(8)),\
              ("i", solver.getIntegerSort())]
    empty = []
    solver.mkRecordSort(fields)
    solver.mkRecordSort(empty)
    recSort = solver.mkRecordSort(fields)
    recSort.getDatatype()


def test_mk_set_sort(solver):
    solver.mkSetSort(solver.getBooleanSort())
    solver.mkSetSort(solver.getIntegerSort())
    solver.mkSetSort(solver.mkBitVectorSort(4))
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkSetSort(solver.mkBitVectorSort(4))


def test_mk_bag_sort(solver):
    solver.mkBagSort(solver.getBooleanSort())
    solver.mkBagSort(solver.getIntegerSort())
    solver.mkBagSort(solver.mkBitVectorSort(4))
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkBagSort(solver.mkBitVectorSort(4))


def test_mk_sequence_sort(solver):
    solver.mkSequenceSort(solver.getBooleanSort())
    solver.mkSequenceSort(\
            solver.mkSequenceSort(solver.getIntegerSort()))
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkSequenceSort(solver.getIntegerSort())


def test_mk_uninterpreted_sort(solver):
    solver.mkUninterpretedSort("u")
    solver.mkUninterpretedSort("")


def test_mk_sortConstructor_sort(solver):
    solver.mkSortConstructorSort("s", 2)
    solver.mkSortConstructorSort("", 2)
    with pytest.raises(RuntimeError):
        solver.mkSortConstructorSort("", 0)


def test_mk_tuple_sort(solver):
    solver.mkTupleSort([solver.getIntegerSort()])
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                                    solver.getIntegerSort())
    with pytest.raises(RuntimeError):
        solver.mkTupleSort([solver.getIntegerSort(), funSort])

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkTupleSort([solver.getIntegerSort()])


def test_mk_bit_vector(solver):
    solver.mkBitVector(8, 2)
    solver.mkBitVector(32, 2)

    solver.mkBitVector(4, "1010", 2)
    solver.mkBitVector(8, "0101", 2)
    solver.mkBitVector(8, "-1111111", 2)
    solver.mkBitVector(8, "00000101", 2)
    solver.mkBitVector(8, "-127", 10)
    solver.mkBitVector(8, "255", 10)
    solver.mkBitVector(10, "1010", 10)
    solver.mkBitVector(11, "1234", 10)
    solver.mkBitVector(8, "-7f", 16)
    solver.mkBitVector(8, "a0", 16)
    solver.mkBitVector(16, "1010", 16)
    solver.mkBitVector(16, "a09f", 16)

    with pytest.raises(RuntimeError):
        solver.mkBitVector(0, 2)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(0, "-127", 10)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(0, "a0", 16)

    with pytest.raises(RuntimeError):
        solver.mkBitVector(2, "", 2)

    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "101", 5)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "127", 11)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "a0", 21)

    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "101010101", 2)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "-11111111", 2)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "-256", 10)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "257", 10)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "-a0", 16)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "fffff", 16)

    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "10201010", 2)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "-25x", 10)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "2x7", 10)
    with pytest.raises(RuntimeError):
        solver.mkBitVector(8, "fzff", 16)

    assert solver.mkBitVector(8, "0101", 2) == solver.mkBitVector(8, "00000101", 2)
    assert solver.mkBitVector(4, "1010", 2) == solver.mkBitVector(4, "10", 10)
    assert solver.mkBitVector(4, "1010", 2) == solver.mkBitVector(4, "a", 16)
    assert str(solver.mkBitVector(8, "01010101", 2)) == "#b01010101"
    assert str(solver.mkBitVector(8, "F", 16)) == "#b00001111"
    assert solver.mkBitVector(8, "-1", 10) ==\
            solver.mkBitVector(8, "FF", 16)


def test_mk_var(solver):
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    funSort = solver.mkFunctionSort(intSort, boolSort)
    solver.mkVar(boolSort)
    solver.mkVar(funSort)
    solver.mkVar(boolSort, "b")
    solver.mkVar(funSort, "")
    with pytest.raises(RuntimeError):
        solver.mkVar(pycvc5.Sort(solver))
    with pytest.raises(RuntimeError):
        solver.mkVar(pycvc5.Sort(solver), "a")
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkVar(boolSort, "x")


def test_mk_boolean(solver):
    solver.mkBoolean(True)
    solver.mkBoolean(False)


def test_mk_rounding_mode(solver):
    solver.mkRoundingMode(pycvc5.RoundTowardZero)


def test_mk_abstract_value(solver):
    solver.mkAbstractValue("1")
    with pytest.raises(ValueError):
        solver.mkAbstractValue("0")
    with pytest.raises(ValueError):
        solver.mkAbstractValue("-1")
    with pytest.raises(ValueError):
        solver.mkAbstractValue("1.2")
    with pytest.raises(ValueError):
        solver.mkAbstractValue("1/2")
    with pytest.raises(ValueError):
        solver.mkAbstractValue("asdf")

    solver.mkAbstractValue(1)
    with pytest.raises(ValueError):
        solver.mkAbstractValue(-1)
    with pytest.raises(ValueError):
        solver.mkAbstractValue(0)


def test_mk_floating_point(solver):
    t1 = solver.mkBitVector(8)
    t2 = solver.mkBitVector(4)
    t3 = solver.mkInteger(2)
    solver.mkFloatingPoint(3, 5, t1)

    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(0, 5, pycvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(0, 5, t1)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(3, 0, t1)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(3, 5, t2)
    with pytest.raises(RuntimeError):
        solver.mkFloatingPoint(3, 5, t2)

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkFloatingPoint(3, 5, t1)

def test_mk_cardinality_constraint(solver):
    su = solver.mkUninterpretedSort("u")
    si = solver.getIntegerSort()
    solver.mkCardinalityConstraint(su, 3)
    with pytest.raises(RuntimeError):
        solver.mkEmptySet(solver.mkCardinalityConstraint(si, 3))
    with pytest.raises(RuntimeError):
        solver.mkEmptySet(solver.mkCardinalityConstraint(su, 0))
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkCardinalityConstraint(su, 3)

def test_mk_empty_set(solver):
    slv = pycvc5.Solver()
    s = solver.mkSetSort(solver.getBooleanSort())
    solver.mkEmptySet(pycvc5.Sort(solver))
    solver.mkEmptySet(s)
    with pytest.raises(RuntimeError):
        solver.mkEmptySet(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        slv.mkEmptySet(s)


def test_mk_empty_bag(solver):
    slv = pycvc5.Solver()
    s = solver.mkBagSort(solver.getBooleanSort())
    solver.mkEmptyBag(pycvc5.Sort(solver))
    solver.mkEmptyBag(s)
    with pytest.raises(RuntimeError):
        solver.mkEmptyBag(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        slv.mkEmptyBag(s)


def test_mk_empty_sequence(solver):
    slv = pycvc5.Solver()
    s = solver.mkSequenceSort(solver.getBooleanSort())
    solver.mkEmptySequence(s)
    solver.mkEmptySequence(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        slv.mkEmptySequence(s)


def test_mk_false(solver):
    solver.mkFalse()
    solver.mkFalse()


def test_mk_nan(solver):
    solver.mkNaN(3, 5)


def test_mk_neg_zero(solver):
    solver.mkNegZero(3, 5)


def test_mk_neg_inf(solver):
    solver.mkNegInf(3, 5)


def test_mk_pos_inf(solver):
    solver.mkPosInf(3, 5)


def test_mk_pos_zero(solver):
    solver.mkPosZero(3, 5)


def test_mk_op(solver):
    # mkOp(Kind kind, Kind k)
    with pytest.raises(ValueError):
        solver.mkOp(kinds.BVExtract, kinds.Equal)

    # mkOp(Kind kind, const std::string& arg)
    solver.mkOp(kinds.Divisible, "2147483648")
    with pytest.raises(RuntimeError):
        solver.mkOp(kinds.BVExtract, "asdf")

    # mkOp(Kind kind, uint32_t arg)
    solver.mkOp(kinds.Divisible, 1)
    solver.mkOp(kinds.BVRotateLeft, 1)
    solver.mkOp(kinds.BVRotateRight, 1)
    with pytest.raises(RuntimeError):
        solver.mkOp(kinds.BVExtract, 1)

    # mkOp(Kind kind, uint32_t arg1, uint32_t arg2)
    solver.mkOp(kinds.BVExtract, 1, 1)
    with pytest.raises(RuntimeError):
        solver.mkOp(kinds.Divisible, 1, 2)

    # mkOp(Kind kind, std::vector<uint32_t> args)
    args = [1, 2, 2]
    solver.mkOp(kinds.TupleProject, args)


def test_mk_pi(solver):
    solver.mkPi()


def test_mk_integer(solver):
    solver.mkInteger("123")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1.23")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1/23")
    with pytest.raises(RuntimeError):
        solver.mkInteger("12/3")
    with pytest.raises(RuntimeError):
        solver.mkInteger(".2")
    with pytest.raises(RuntimeError):
        solver.mkInteger("2.")
    with pytest.raises(RuntimeError):
        solver.mkInteger("")
    with pytest.raises(RuntimeError):
        solver.mkInteger("asdf")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1.2/3")
    with pytest.raises(RuntimeError):
        solver.mkInteger(".")
    with pytest.raises(RuntimeError):
        solver.mkInteger("/")
    with pytest.raises(RuntimeError):
        solver.mkInteger("2/")
    with pytest.raises(RuntimeError):
        solver.mkInteger("/2")

    solver.mkReal("123")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1.23")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1/23")
    with pytest.raises(RuntimeError):
        solver.mkInteger("12/3")
    with pytest.raises(RuntimeError):
        solver.mkInteger(".2")
    with pytest.raises(RuntimeError):
        solver.mkInteger("2.")
    with pytest.raises(RuntimeError):
        solver.mkInteger("")
    with pytest.raises(RuntimeError):
        solver.mkInteger("asdf")
    with pytest.raises(RuntimeError):
        solver.mkInteger("1.2/3")
    with pytest.raises(RuntimeError):
        solver.mkInteger(".")
    with pytest.raises(RuntimeError):
        solver.mkInteger("/")
    with pytest.raises(RuntimeError):
        solver.mkInteger("2/")
    with pytest.raises(RuntimeError):
        solver.mkInteger("/2")

    val1 = 1
    val2 = -1
    val3 = 1
    val4 = -1
    solver.mkInteger(val1)
    solver.mkInteger(val2)
    solver.mkInteger(val3)
    solver.mkInteger(val4)
    solver.mkInteger(val4)


def test_mk_real(solver):
    solver.mkReal("123")
    solver.mkReal("1.23")
    solver.mkReal("1/23")
    solver.mkReal("12/3")
    solver.mkReal(".2")
    solver.mkReal("2.")
    with pytest.raises(RuntimeError):
        solver.mkReal("")
    with pytest.raises(RuntimeError):
        solver.mkReal("asdf")
    with pytest.raises(RuntimeError):
        solver.mkReal("1.2/3")
    with pytest.raises(RuntimeError):
        solver.mkReal(".")
    with pytest.raises(RuntimeError):
        solver.mkReal("/")
    with pytest.raises(RuntimeError):
        solver.mkReal("2/")
    with pytest.raises(RuntimeError):
        solver.mkReal("/2")

    solver.mkReal("123")
    solver.mkReal("1.23")
    solver.mkReal("1/23")
    solver.mkReal("12/3")
    solver.mkReal(".2")
    solver.mkReal("2.")
    with pytest.raises(RuntimeError):
        solver.mkReal("")
    with pytest.raises(RuntimeError):
        solver.mkReal("asdf")
    with pytest.raises(RuntimeError):
        solver.mkReal("1.2/3")
    with pytest.raises(RuntimeError):
        solver.mkReal(".")
    with pytest.raises(RuntimeError):
        solver.mkReal("/")
    with pytest.raises(RuntimeError):
        solver.mkReal("2/")
    with pytest.raises(RuntimeError):
        solver.mkReal("/2")

    val1 = 1
    val2 = -1
    val3 = 1
    val4 = -1
    solver.mkReal(val1)
    solver.mkReal(val2)
    solver.mkReal(val3)
    solver.mkReal(val4)
    solver.mkReal(val4)
    solver.mkReal(val1, val1)
    solver.mkReal(val2, val2)
    solver.mkReal(val3, val3)
    solver.mkReal(val4, val4)


def test_mk_regexp_none(solver):
    strSort = solver.getStringSort()
    s = solver.mkConst(strSort, "s")
    solver.mkTerm(kinds.StringInRegexp, s, solver.mkRegexpNone())


def test_mk_regexp_all(solver):
    strSort = solver.getStringSort()
    s = solver.mkConst(strSort, "s")
    solver.mkTerm(kinds.StringInRegexp, s, solver.mkRegexpAll())


def test_mk_regexp_allchar(solver):
    strSort = solver.getStringSort()
    s = solver.mkConst(strSort, "s")
    solver.mkTerm(kinds.StringInRegexp, s, solver.mkRegexpAllchar())


def test_mk_sep_emp(solver):
    solver.mkSepEmp();


def test_mk_sep_nil(solver):
    solver.mkSepNil(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        solver.mkSepNil(pycvc5.Sort(solver))
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkSepNil(solver.getIntegerSort())


def test_mk_string(solver):
    solver.mkString("")
    solver.mkString("asdfasdf")
    str(solver.mkString("asdf\\nasdf")) == "\"asdf\\u{5c}nasdf\""
    str(solver.mkString("asdf\\u{005c}nasdf", True)) ==\
            "\"asdf\\u{5c}nasdf\""


def test_mk_term(solver):
    bv32 = solver.mkBitVectorSort(32)
    a = solver.mkConst(bv32, "a")
    b = solver.mkConst(bv32, "b")
    v1 = [a, b]
    v2 = [a, pycvc5.Term(solver)]
    v3 = [a, solver.mkTrue()]
    v4 = [solver.mkInteger(1), solver.mkInteger(2)]
    v5 = [solver.mkInteger(1), pycvc5.Term(solver)]
    v6 = []
    slv = pycvc5.Solver()

    # mkTerm(Kind kind) const
    solver.mkPi()
    solver.mkTerm(kinds.RegexpNone)
    solver.mkTerm(kinds.RegexpAllchar)
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.ConstBV)

    # mkTerm(Kind kind, Term child) const
    solver.mkTerm(kinds.Not, solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.Not, pycvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.Not, a)
    with pytest.raises(RuntimeError):
        slv.mkTerm(kinds.Not, solver.mkTrue())

    # mkTerm(Kind kind, Term child1, Term child2) const
    solver.mkTerm(kinds.Equal, a, b)
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.Equal, pycvc5.Term(solver), b)
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.Equal, a, pycvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.Equal, a, solver.mkTrue())
    with pytest.raises(RuntimeError):
        slv.mkTerm(kinds.Equal, a, b)

    # mkTerm(Kind kind, Term child1, Term child2, Term child3) const
    solver.mkTerm(kinds.Ite, solver.mkTrue(), solver.mkTrue(), solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.Ite, pycvc5.Term(solver), solver.mkTrue(),
                      solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.Ite, solver.mkTrue(), pycvc5.Term(solver),
                      solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.Ite, solver.mkTrue(), solver.mkTrue(),
                      pycvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.Ite, solver.mkTrue(), solver.mkTrue(), b)
    with pytest.raises(RuntimeError):
        slv.mkTerm(kinds.Ite, solver.mkTrue(), solver.mkTrue(),
                   solver.mkTrue())

    # mkTerm(Kind kind, const std::vector<Term>& children) const
    solver.mkTerm(kinds.Equal, v1)
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.Equal, v2)
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.Equal, v3)
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.Distinct, v6)


def test_mk_term_from_op(solver):
    bv32 = solver.mkBitVectorSort(32)
    a = solver.mkConst(bv32, "a")
    b = solver.mkConst(bv32, "b")
    v1 = [solver.mkInteger(1), solver.mkInteger(2)]
    v2 = [solver.mkInteger(1), pycvc5.Term(solver)]
    v3 = []
    v4 = [solver.mkInteger(5)]
    slv = pycvc5.Solver()

    # simple operator terms
    opterm1 = solver.mkOp(kinds.BVExtract, 2, 1)
    opterm2 = solver.mkOp(kinds.Divisible, 1)

    # list datatype
    sort = solver.mkParamSort("T")
    listDecl = solver.mkDatatypeDecl("paramlist", sort)
    cons = solver.mkDatatypeConstructorDecl("cons")
    nil = solver.mkDatatypeConstructorDecl("nil")
    cons.addSelector("head", sort)
    cons.addSelectorSelf("tail")
    listDecl.addConstructor(cons)
    listDecl.addConstructor(nil)
    listSort = solver.mkDatatypeSort(listDecl)
    intListSort =\
        listSort.instantiate([solver.getIntegerSort()])
    c = solver.mkConst(intListSort, "c")
    lis = listSort.getDatatype()

    # list datatype constructor and selector operator terms
    consTerm1 = lis.getConstructorTerm("cons")
    consTerm2 = lis.getConstructor("cons").getConstructorTerm()
    nilTerm1 = lis.getConstructorTerm("nil")
    nilTerm2 = lis.getConstructor("nil").getConstructorTerm()
    headTerm1 = lis["cons"].getSelectorTerm("head")
    headTerm2 = lis["cons"].getSelector("head").getSelectorTerm()
    tailTerm1 = lis["cons"].getSelectorTerm("tail")
    tailTerm2 = lis["cons"]["tail"].getSelectorTerm()

    # mkTerm(Op op, Term term) const
    solver.mkTerm(kinds.ApplyConstructor, nilTerm1)
    solver.mkTerm(kinds.ApplyConstructor, nilTerm2)
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.ApplySelector, nilTerm1)
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.ApplySelector, consTerm1)
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.ApplyConstructor, consTerm2)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm1)
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.ApplySelector, headTerm1)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm1)
    with pytest.raises(RuntimeError):
        slv.mkTerm(kinds.ApplyConstructor, nilTerm1)

    # mkTerm(Op op, Term child) const
    solver.mkTerm(opterm1, a)
    solver.mkTerm(opterm2, solver.mkInteger(1))
    solver.mkTerm(kinds.ApplySelector, headTerm1, c)
    solver.mkTerm(kinds.ApplySelector, tailTerm2, c)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, a)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm1, pycvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkTerm(kinds.ApplyConstructor, consTerm1, solver.mkInteger(0))
    with pytest.raises(RuntimeError):
        slv.mkTerm(opterm1, a)

    # mkTerm(Op op, Term child1, Term child2) const
    solver.mkTerm(kinds.ApplyConstructor, consTerm1, solver.mkInteger(0),
                  solver.mkTerm(kinds.ApplyConstructor, nilTerm1))
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, solver.mkInteger(1), solver.mkInteger(2))
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm1, a, b)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, solver.mkInteger(1), pycvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, pycvc5.Term(solver), solver.mkInteger(1))
    with pytest.raises(RuntimeError):
        slv.mkTerm(kinds.ApplyConstructor,\
                        consTerm1,\
                        solver.mkInteger(0),\
                        solver.mkTerm(kinds.ApplyConstructor, nilTerm1))

    # mkTerm(Op op, Term child1, Term child2, Term child3) const
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm1, a, b, a)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, solver.mkInteger(1), solver.mkInteger(1),
                      pycvc5.Term(solver))

    # mkTerm(Op op, const std::vector<Term>& children) const
    solver.mkTerm(opterm2, v4)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, v1)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, v2)
    with pytest.raises(RuntimeError):
        solver.mkTerm(opterm2, v3)
    with pytest.raises(RuntimeError):
        slv.mkTerm(opterm2, v4)


def test_mk_true(solver):
    solver.mkTrue()
    solver.mkTrue()


def test_mk_tuple(solver):
    solver.mkTuple([solver.mkBitVectorSort(3)], [solver.mkBitVector(3, "101", 2)])
    solver.mkTuple([solver.getRealSort()], [solver.mkInteger("5")])

    with pytest.raises(RuntimeError):
        solver.mkTuple([], [solver.mkBitVector(3, "101", 2)])
    with pytest.raises(RuntimeError):
        solver.mkTuple([solver.mkBitVectorSort(4)],
                       [solver.mkBitVector(3, "101", 2)])
    with pytest.raises(RuntimeError):
        solver.mkTuple([solver.getIntegerSort()], [solver.mkReal("5.3")])
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkTuple([solver.mkBitVectorSort(3)], [slv.mkBitVector(3, "101", 2)])
    with pytest.raises(RuntimeError):
        slv.mkTuple([slv.mkBitVectorSort(3)], [solver.mkBitVector(3, "101", 2)])


def test_mk_universe_set(solver):
    solver.mkUniverseSet(solver.getBooleanSort())
    with pytest.raises(RuntimeError):
        solver.mkUniverseSet(pycvc5.Sort(solver))
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkUniverseSet(solver.getBooleanSort())


def test_mk_const(solver):
    boolSort = solver.getBooleanSort()
    intSort = solver.getIntegerSort()
    funSort = solver.mkFunctionSort(intSort, boolSort)
    solver.mkConst(boolSort)
    solver.mkConst(funSort)
    solver.mkConst(boolSort, "b")
    solver.mkConst(intSort, "i")
    solver.mkConst(funSort, "f")
    solver.mkConst(funSort, "")
    with pytest.raises(RuntimeError):
        solver.mkConst(pycvc5.Sort(solver))
    with pytest.raises(RuntimeError):
        solver.mkConst(pycvc5.Sort(solver), "a")

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.mkConst(boolSort)


def test_mk_const_array(solver):
    intSort = solver.getIntegerSort()
    arrSort = solver.mkArraySort(intSort, intSort)
    zero = solver.mkInteger(0)
    constArr = solver.mkConstArray(arrSort, zero)

    solver.mkConstArray(arrSort, zero)
    with pytest.raises(RuntimeError):
        solver.mkConstArray(pycvc5.Sort(solver), zero)
    with pytest.raises(RuntimeError):
        solver.mkConstArray(arrSort, pycvc5.Term(solver))
    with pytest.raises(RuntimeError):
        solver.mkConstArray(arrSort, solver.mkBitVector(1, 1))
    with pytest.raises(RuntimeError):
        solver.mkConstArray(intSort, zero)
    slv = pycvc5.Solver()
    zero2 = slv.mkInteger(0)
    arrSort2 = slv.mkArraySort(slv.getIntegerSort(), slv.getIntegerSort())
    with pytest.raises(RuntimeError):
        slv.mkConstArray(arrSort2, zero)
    with pytest.raises(RuntimeError):
        slv.mkConstArray(arrSort, zero2)


def test_declare_fun(solver):
    bvSort = solver.mkBitVectorSort(32)
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                                    solver.getIntegerSort())
    solver.declareFun("f1", [], bvSort)
    solver.declareFun("f3", [bvSort, solver.getIntegerSort()], bvSort)
    with pytest.raises(RuntimeError):
        solver.declareFun("f2", [], funSort)
    # functions as arguments is allowed
    solver.declareFun("f4", [bvSort, funSort], bvSort)
    with pytest.raises(RuntimeError):
        solver.declareFun("f5", [bvSort, bvSort], funSort)
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.declareFun("f1", [], bvSort)


def test_declare_sort(solver):
    solver.declareSort("s", 0)
    solver.declareSort("s", 2)
    solver.declareSort("", 2)


def test_define_fun(solver):
    bvSort = solver.mkBitVectorSort(32)
    funSort = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),
                                    solver.getIntegerSort())
    b1 = solver.mkVar(bvSort, "b1")
    b2 = solver.mkVar(solver.getIntegerSort(), "b2")
    b3 = solver.mkVar(funSort, "b3")
    v1 = solver.mkConst(bvSort, "v1")
    v2 = solver.mkConst(funSort, "v2")
    solver.defineFun("f", [], bvSort, v1)
    solver.defineFun("ff", [b1, b2], bvSort, v1)
    with pytest.raises(RuntimeError):
        solver.defineFun("ff", [v1, b2], bvSort, v1)
    with pytest.raises(RuntimeError):
        solver.defineFun("fff", [b1], bvSort, v2)
    with pytest.raises(RuntimeError):
        solver.defineFun("ffff", [b1], funSort, v2)
    # b3 has function sort, which is allowed as an argument
    solver.defineFun("fffff", [b1, b3], bvSort, v1)

    slv = pycvc5.Solver()
    bvSort2 = slv.mkBitVectorSort(32)
    v12 = slv.mkConst(bvSort2, "v1")
    b12 = slv.mkVar(bvSort2, "b1")
    b22 = slv.mkVar(slv.getIntegerSort(), "b2")
    with pytest.raises(RuntimeError):
        slv.defineFun("f", [], bvSort, v12)
    with pytest.raises(RuntimeError):
        slv.defineFun("f", [], bvSort2, v1)
    with pytest.raises(RuntimeError):
        slv.defineFun("ff", [b1, b22], bvSort2, v12)
    with pytest.raises(RuntimeError):
        slv.defineFun("ff", [b12, b2], bvSort2, v12)
    with pytest.raises(RuntimeError):
        slv.defineFun("ff", [b12, b22], bvSort, v12)
    with pytest.raises(RuntimeError):
        slv.defineFun("ff", [b12, b22], bvSort2, v1)


def test_define_fun_rec(solver):
    bvSort = solver.mkBitVectorSort(32)
    funSort1 = solver.mkFunctionSort([bvSort, bvSort], bvSort)
    funSort2 = solver.mkFunctionSort(solver.mkUninterpretedSort("u"),\
                                     solver.getIntegerSort())
    b1 = solver.mkVar(bvSort, "b1")
    b11 = solver.mkVar(bvSort, "b1")
    b2 = solver.mkVar(solver.getIntegerSort(), "b2")
    b3 = solver.mkVar(funSort2, "b3")
    v1 = solver.mkConst(bvSort, "v1")
    v2 = solver.mkConst(solver.getIntegerSort(), "v2")
    v3 = solver.mkConst(funSort2, "v3")
    f1 = solver.mkConst(funSort1, "f1")
    f2 = solver.mkConst(funSort2, "f2")
    f3 = solver.mkConst(bvSort, "f3")
    solver.defineFunRec("f", [], bvSort, v1)
    solver.defineFunRec("ff", [b1, b2], bvSort, v1)
    solver.defineFunRec(f1, [b1, b11], v1)
    with pytest.raises(RuntimeError):
        solver.defineFunRec("fff", [b1], bvSort, v3)
    with pytest.raises(RuntimeError):
        solver.defineFunRec("ff", [b1, v2], bvSort, v1)
    with pytest.raises(RuntimeError):
        solver.defineFunRec("ffff", [b1], funSort2, v3)
    # b3 has function sort, which is allowed as an argument
    solver.defineFunRec("fffff", [b1, b3], bvSort, v1)
    with pytest.raises(RuntimeError):
        solver.defineFunRec(f1, [b1], v1)
    with pytest.raises(RuntimeError):
        solver.defineFunRec(f1, [b1, b11], v2)
    with pytest.raises(RuntimeError):
        solver.defineFunRec(f1, [b1, b11], v3)
    with pytest.raises(RuntimeError):
        solver.defineFunRec(f2, [b1], v2)
    with pytest.raises(RuntimeError):
        solver.defineFunRec(f3, [b1], v1)

    slv = pycvc5.Solver()
    bvSort2 = slv.mkBitVectorSort(32)
    v12 = slv.mkConst(bvSort2, "v1")
    b12 = slv.mkVar(bvSort2, "b1")
    b22 = slv.mkVar(slv.getIntegerSort(), "b2")
    slv.defineFunRec("f", [], bvSort2, v12)
    slv.defineFunRec("ff", [b12, b22], bvSort2, v12)
    with pytest.raises(RuntimeError):
        slv.defineFunRec("f", [], bvSort, v12)
    with pytest.raises(RuntimeError):
        slv.defineFunRec("f", [], bvSort2, v1)
    with pytest.raises(RuntimeError):
        slv.defineFunRec("ff", [b1, b22], bvSort2, v12)
    with pytest.raises(RuntimeError):
        slv.defineFunRec("ff", [b12, b2], bvSort2, v12)
    with pytest.raises(RuntimeError):
        slv.defineFunRec("ff", [b12, b22], bvSort, v12)
    with pytest.raises(RuntimeError):
        slv.defineFunRec("ff", [b12, b22], bvSort2, v1)


def test_define_fun_rec_wrong_logic(solver):
    solver.setLogic("QF_BV")
    bvSort = solver.mkBitVectorSort(32)
    funSort = solver.mkFunctionSort([bvSort, bvSort], bvSort)
    b = solver.mkVar(bvSort, "b")
    v = solver.mkConst(bvSort, "v")
    f = solver.mkConst(funSort, "f")
    with pytest.raises(RuntimeError):
        solver.defineFunRec("f", [], bvSort, v)
    with pytest.raises(RuntimeError):
        solver.defineFunRec(f, [b, b], v)


def test_uf_iteration(solver):
    intSort = solver.getIntegerSort()
    funSort = solver.mkFunctionSort([intSort, intSort], intSort)
    x = solver.mkConst(intSort, "x")
    y = solver.mkConst(intSort, "y")
    f = solver.mkConst(funSort, "f")
    fxy = solver.mkTerm(kinds.ApplyUf, f, x, y)

    # Expecting the uninterpreted function to be one of the children
    expected_children = [f, x, y]
    idx = 0
    for c in fxy:
        assert idx < 3
        assert c == expected_children[idx]
        idx = idx + 1


def test_get_info(solver):
    solver.getInfo("name")
    with pytest.raises(RuntimeError):
        solver.getInfo("asdf")


def test_get_op(solver):
    bv32 = solver.mkBitVectorSort(32)
    a = solver.mkConst(bv32, "a")
    ext = solver.mkOp(kinds.BVExtract, 2, 1)
    exta = solver.mkTerm(ext, a)

    assert not a.hasOp()
    with pytest.raises(RuntimeError):
        a.getOp()
    assert exta.hasOp()
    assert exta.getOp() == ext

    # Test Datatypes -- more complicated
    consListSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    cons.addSelectorSelf("tail")
    consListSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    consListSpec.addConstructor(nil)
    consListSort = solver.mkDatatypeSort(consListSpec)
    consList = consListSort.getDatatype()

    consTerm = consList.getConstructorTerm("cons")
    nilTerm = consList.getConstructorTerm("nil")
    headTerm = consList["cons"].getSelectorTerm("head")

    listnil = solver.mkTerm(kinds.ApplyConstructor, nilTerm)
    listcons1 = solver.mkTerm(kinds.ApplyConstructor, consTerm,
                              solver.mkInteger(1), listnil)
    listhead = solver.mkTerm(kinds.ApplySelector, headTerm, listcons1)

    assert listnil.hasOp()
    assert listcons1.hasOp()
    assert listhead.hasOp()


def test_get_option(solver):
    solver.getOption("incremental")
    with pytest.raises(RuntimeError):
        solver.getOption("asdf")


def test_get_unsat_assumptions1(solver):
    solver.setOption("incremental", "false")
    solver.checkSatAssuming(solver.mkFalse())
    with pytest.raises(RuntimeError):
        solver.getUnsatAssumptions()


def test_get_unsat_assumptions2(solver):
    solver.setOption("incremental", "true")
    solver.setOption("produce-unsat-assumptions", "false")
    solver.checkSatAssuming(solver.mkFalse())
    with pytest.raises(RuntimeError):
        solver.getUnsatAssumptions()


def test_get_unsat_assumptions3(solver):
    solver.setOption("incremental", "true")
    solver.setOption("produce-unsat-assumptions", "true")
    solver.checkSatAssuming(solver.mkFalse())
    solver.getUnsatAssumptions()
    solver.checkSatAssuming(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.getUnsatAssumptions()


def test_get_unsat_core1(solver):
    solver.setOption("incremental", "false")
    solver.assertFormula(solver.mkFalse())
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getUnsatCore()


def test_get_unsat_core2(solver):
    solver.setOption("incremental", "false")
    solver.setOption("produce-unsat-cores", "false")
    solver.assertFormula(solver.mkFalse())
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getUnsatCore()


def test_get_unsat_core3(solver):
    solver.setOption("incremental", "true")
    solver.setOption("produce-unsat-cores", "true")

    uSort = solver.mkUninterpretedSort("u")
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    uToIntSort = solver.mkFunctionSort(uSort, intSort)
    intPredSort = solver.mkFunctionSort(intSort, boolSort)

    x = solver.mkConst(uSort, "x")
    y = solver.mkConst(uSort, "y")
    f = solver.mkConst(uToIntSort, "f")
    p = solver.mkConst(intPredSort, "p")
    zero = solver.mkInteger(0)
    one = solver.mkInteger(1)
    f_x = solver.mkTerm(kinds.ApplyUf, f, x)
    f_y = solver.mkTerm(kinds.ApplyUf, f, y)
    summ = solver.mkTerm(kinds.Plus, f_x, f_y)
    p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
    p_f_y = solver.mkTerm(kinds.ApplyUf, p, f_y)
    solver.assertFormula(solver.mkTerm(kinds.Gt, zero, f_x))
    solver.assertFormula(solver.mkTerm(kinds.Gt, zero, f_y))
    solver.assertFormula(solver.mkTerm(kinds.Gt, summ, one))
    solver.assertFormula(p_0)
    solver.assertFormula(p_f_y.notTerm())
    assert solver.checkSat().isUnsat()

    unsat_core = solver.getUnsatCore()

    solver.resetAssertions()
    for t in unsat_core:
        solver.assertFormula(t)
    res = solver.checkSat()
    assert res.isUnsat()


def test_get_value1(solver):
    solver.setOption("produce-models", "false")
    t = solver.mkTrue()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValue(t)


def test_get_value2(solver):
    solver.setOption("produce-models", "true")
    t = solver.mkFalse()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValue(t)


def test_get_value3(solver):
    solver.setOption("produce-models", "true")
    uSort = solver.mkUninterpretedSort("u")
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    uToIntSort = solver.mkFunctionSort(uSort, intSort)
    intPredSort = solver.mkFunctionSort(intSort, boolSort)

    x = solver.mkConst(uSort, "x")
    y = solver.mkConst(uSort, "y")
    z = solver.mkConst(uSort, "z")
    f = solver.mkConst(uToIntSort, "f")
    p = solver.mkConst(intPredSort, "p")
    zero = solver.mkInteger(0)
    one = solver.mkInteger(1)
    f_x = solver.mkTerm(kinds.ApplyUf, f, x)
    f_y = solver.mkTerm(kinds.ApplyUf, f, y)
    summ = solver.mkTerm(kinds.Plus, f_x, f_y)
    p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
    p_f_y = solver.mkTerm(kinds.ApplyUf, p, f_y)

    solver.assertFormula(solver.mkTerm(kinds.Leq, zero, f_x))
    solver.assertFormula(solver.mkTerm(kinds.Leq, zero, f_y))
    solver.assertFormula(solver.mkTerm(kinds.Leq, summ, one))
    solver.assertFormula(p_0.notTerm())
    solver.assertFormula(p_f_y)
    assert solver.checkSat().isSat()
    solver.getValue(x)
    solver.getValue(y)
    solver.getValue(z)
    solver.getValue(summ)
    solver.getValue(p_f_y)

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.getValue(x)


def test_declare_sep_heap(solver):
    solver.setLogic("ALL")
    integer = solver.getIntegerSort()
    solver.declareSepHeap(integer, integer)
    # cannot declare separation logic heap more than once
    with pytest.raises(RuntimeError):
        solver.declareSepHeap(integer, integer)


# Helper function for test_get_separation_{heap,nil}_termX. Asserts and checks
# some simple separation logic constraints.
def checkSimpleSeparationConstraints(slv):
    integer = slv.getIntegerSort()
    # declare the separation heap
    slv.declareSepHeap(integer, integer)
    x = slv.mkConst(integer, "x")
    p = slv.mkConst(integer, "p")
    heap = slv.mkTerm(kinds.SepPto, p, x)
    slv.assertFormula(heap)
    nil = slv.mkSepNil(integer)
    slv.assertFormula(nil.eqTerm(slv.mkReal(5)))
    slv.checkSat()


def test_get_value_sep_heap_1(solver):
    solver.setLogic("QF_BV")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkTrue()
    solver.assertFormula(t)
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap_2(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "false")
    checkSimpleSeparationConstraints(solver)
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap_3(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkFalse()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap_4(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkTrue()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepHeap()


def test_get_value_sep_heap_5(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    checkSimpleSeparationConstraints(solver)
    solver.getValueSepHeap()


def test_get_value_sep_nil_1(solver):
    solver.setLogic("QF_BV")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkTrue()
    solver.assertFormula(t)
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil_2(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "false")
    checkSimpleSeparationConstraints(solver)
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil_3(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkFalse()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil_4(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    t = solver.mkTrue()
    solver.assertFormula(t)
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.getValueSepNil()


def test_get_value_sep_nil_5(solver):
    solver.setLogic("ALL")
    solver.setOption("incremental", "false")
    solver.setOption("produce-models", "true")
    checkSimpleSeparationConstraints(solver)
    solver.getValueSepNil()


def test_push1(solver):
    solver.setOption("incremental", "true")
    solver.push(1)
    with pytest.raises(RuntimeError):
        solver.setOption("incremental", "false")
    with pytest.raises(RuntimeError):
        solver.setOption("incremental", "true")


def test_push2(solver):
    solver.setOption("incremental", "false")
    with pytest.raises(RuntimeError):
        solver.push(1)


def test_pop1(solver):
    solver.setOption("incremental", "false")
    with pytest.raises(RuntimeError):
        solver.pop(1)


def test_pop2(solver):
    solver.setOption("incremental", "true")
    with pytest.raises(RuntimeError):
        solver.pop(1)


def test_pop3(solver):
    solver.setOption("incremental", "true")
    solver.push(1)
    solver.pop(1)
    with pytest.raises(RuntimeError):
        solver.pop(1)


def test_setInfo(solver):
    with pytest.raises(RuntimeError):
        solver.setInfo("cvc5-lagic", "QF_BV")
    with pytest.raises(RuntimeError):
        solver.setInfo("cvc2-logic", "QF_BV")
    with pytest.raises(RuntimeError):
        solver.setInfo("cvc5-logic", "asdf")

    solver.setInfo("source", "asdf")
    solver.setInfo("category", "asdf")
    solver.setInfo("difficulty", "asdf")
    solver.setInfo("filename", "asdf")
    solver.setInfo("license", "asdf")
    solver.setInfo("name", "asdf")
    solver.setInfo("notes", "asdf")

    solver.setInfo("smt-lib-version", "2")
    solver.setInfo("smt-lib-version", "2.0")
    solver.setInfo("smt-lib-version", "2.5")
    solver.setInfo("smt-lib-version", "2.6")
    with pytest.raises(RuntimeError):
        solver.setInfo("smt-lib-version", ".0")

    solver.setInfo("status", "sat")
    solver.setInfo("status", "unsat")
    solver.setInfo("status", "unknown")
    with pytest.raises(RuntimeError):
        solver.setInfo("status", "asdf")


def test_simplify(solver):
    with pytest.raises(RuntimeError):
        solver.simplify(pycvc5.Term(solver))

    bvSort = solver.mkBitVectorSort(32)
    uSort = solver.mkUninterpretedSort("u")
    funSort1 = solver.mkFunctionSort([bvSort, bvSort], bvSort)
    funSort2 = solver.mkFunctionSort(uSort, solver.getIntegerSort())
    consListSpec = solver.mkDatatypeDecl("list")
    cons = solver.mkDatatypeConstructorDecl("cons")
    cons.addSelector("head", solver.getIntegerSort())
    cons.addSelectorSelf("tail")
    consListSpec.addConstructor(cons)
    nil = solver.mkDatatypeConstructorDecl("nil")
    consListSpec.addConstructor(nil)
    consListSort = solver.mkDatatypeSort(consListSpec)

    x = solver.mkConst(bvSort, "x")
    solver.simplify(x)
    a = solver.mkConst(bvSort, "a")
    solver.simplify(a)
    b = solver.mkConst(bvSort, "b")
    solver.simplify(b)
    x_eq_x = solver.mkTerm(kinds.Equal, x, x)
    solver.simplify(x_eq_x)
    assert solver.mkTrue() != x_eq_x
    assert solver.mkTrue() == solver.simplify(x_eq_x)
    x_eq_b = solver.mkTerm(kinds.Equal, x, b)
    solver.simplify(x_eq_b)
    assert solver.mkTrue() != x_eq_b
    assert solver.mkTrue() != solver.simplify(x_eq_b)
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.simplify(x)

    i1 = solver.mkConst(solver.getIntegerSort(), "i1")
    solver.simplify(i1)
    i2 = solver.mkTerm(kinds.Mult, i1, solver.mkInteger("23"))
    solver.simplify(i2)
    assert i1 != i2
    assert i1 != solver.simplify(i2)
    i3 = solver.mkTerm(kinds.Plus, i1, solver.mkInteger(0))
    solver.simplify(i3)
    assert i1 != i3
    assert i1 == solver.simplify(i3)

    consList = consListSort.getDatatype()
    dt1 = solver.mkTerm(\
        kinds.ApplyConstructor,\
        consList.getConstructorTerm("cons"),\
        solver.mkInteger(0),\
        solver.mkTerm(kinds.ApplyConstructor, consList.getConstructorTerm("nil")))
    solver.simplify(dt1)
    dt2 = solver.mkTerm(\
      kinds.ApplySelector, consList["cons"].getSelectorTerm("head"), dt1)
    solver.simplify(dt2)

    b1 = solver.mkVar(bvSort, "b1")
    solver.simplify(b1)
    b2 = solver.mkVar(bvSort, "b1")
    solver.simplify(b2)
    b3 = solver.mkVar(uSort, "b3")
    solver.simplify(b3)
    v1 = solver.mkConst(bvSort, "v1")
    solver.simplify(v1)
    v2 = solver.mkConst(solver.getIntegerSort(), "v2")
    solver.simplify(v2)
    f1 = solver.mkConst(funSort1, "f1")
    solver.simplify(f1)
    f2 = solver.mkConst(funSort2, "f2")
    solver.simplify(f2)
    solver.defineFunsRec([f1, f2], [[b1, b2], [b3]], [v1, v2])
    solver.simplify(f1)
    solver.simplify(f2)


def test_assert_formula(solver):
    solver.assertFormula(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.assertFormula(pycvc5.Term(solver))
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.assertFormula(solver.mkTrue())


def test_check_entailed(solver):
    solver.setOption("incremental", "false")
    solver.checkEntailed(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.checkEntailed(solver.mkTrue())
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.checkEntailed(solver.mkTrue())


def test_check_entailed1(solver):
    boolSort = solver.getBooleanSort()
    x = solver.mkConst(boolSort, "x")
    y = solver.mkConst(boolSort, "y")
    z = solver.mkTerm(kinds.And, x, y)
    solver.setOption("incremental", "true")
    solver.checkEntailed(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.checkEntailed(pycvc5.Term(solver))
    solver.checkEntailed(solver.mkTrue())
    solver.checkEntailed(z)
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.checkEntailed(solver.mkTrue())


def test_check_entailed2(solver):
    solver.setOption("incremental", "true")

    uSort = solver.mkUninterpretedSort("u")
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    uToIntSort = solver.mkFunctionSort(uSort, intSort)
    intPredSort = solver.mkFunctionSort(intSort, boolSort)

    n = pycvc5.Term(solver)
    # Constants
    x = solver.mkConst(uSort, "x")
    y = solver.mkConst(uSort, "y")
    # Functions
    f = solver.mkConst(uToIntSort, "f")
    p = solver.mkConst(intPredSort, "p")
    # Values
    zero = solver.mkInteger(0)
    one = solver.mkInteger(1)
    # Terms
    f_x = solver.mkTerm(kinds.ApplyUf, f, x)
    f_y = solver.mkTerm(kinds.ApplyUf, f, y)
    summ = solver.mkTerm(kinds.Plus, f_x, f_y)
    p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
    p_f_y = solver.mkTerm(kinds.ApplyUf, p, f_y)
    # Assertions
    assertions =\
        solver.mkTerm(kinds.And,\
                      [solver.mkTerm(kinds.Leq, zero, f_x),  # 0 <= f(x)
                       solver.mkTerm(kinds.Leq, zero, f_y),  # 0 <= f(y)
                       solver.mkTerm(kinds.Leq, summ, one),  # f(x) + f(y) <= 1
                       p_0.notTerm(),                        # not p(0)
                       p_f_y                                 # p(f(y))
                      ])

    solver.checkEntailed(solver.mkTrue())
    solver.assertFormula(assertions)
    solver.checkEntailed(solver.mkTerm(kinds.Distinct, x, y))
    solver.checkEntailed(\
        [solver.mkFalse(), solver.mkTerm(kinds.Distinct, x, y)])
    with pytest.raises(RuntimeError):
        solver.checkEntailed(n)
    with pytest.raises(RuntimeError):
        solver.checkEntailed([n, solver.mkTerm(kinds.Distinct, x, y)])
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.checkEntailed(solver.mkTrue())


def test_check_sat(solver):
    solver.setOption("incremental", "false")
    solver.checkSat()
    with pytest.raises(RuntimeError):
        solver.checkSat()


def test_check_sat_assuming(solver):
    solver.setOption("incremental", "false")
    solver.checkSatAssuming(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.checkSatAssuming(solver.mkTrue())
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.checkSatAssuming(solver.mkTrue())


def test_check_sat_assuming1(solver):
    boolSort = solver.getBooleanSort()
    x = solver.mkConst(boolSort, "x")
    y = solver.mkConst(boolSort, "y")
    z = solver.mkTerm(kinds.And, x, y)
    solver.setOption("incremental", "true")
    solver.checkSatAssuming(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.checkSatAssuming(pycvc5.Term(solver))
    solver.checkSatAssuming(solver.mkTrue())
    solver.checkSatAssuming(z)
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.checkSatAssuming(solver.mkTrue())


def test_check_sat_assuming2(solver):
    solver.setOption("incremental", "true")

    uSort = solver.mkUninterpretedSort("u")
    intSort = solver.getIntegerSort()
    boolSort = solver.getBooleanSort()
    uToIntSort = solver.mkFunctionSort(uSort, intSort)
    intPredSort = solver.mkFunctionSort(intSort, boolSort)

    n = pycvc5.Term(solver)
    # Constants
    x = solver.mkConst(uSort, "x")
    y = solver.mkConst(uSort, "y")
    # Functions
    f = solver.mkConst(uToIntSort, "f")
    p = solver.mkConst(intPredSort, "p")
    # Values
    zero = solver.mkInteger(0)
    one = solver.mkInteger(1)
    # Terms
    f_x = solver.mkTerm(kinds.ApplyUf, f, x)
    f_y = solver.mkTerm(kinds.ApplyUf, f, y)
    summ = solver.mkTerm(kinds.Plus, f_x, f_y)
    p_0 = solver.mkTerm(kinds.ApplyUf, p, zero)
    p_f_y = solver.mkTerm(kinds.ApplyUf, p, f_y)
    # Assertions
    assertions =\
        solver.mkTerm(kinds.And,\
                      [solver.mkTerm(kinds.Leq, zero, f_x),  # 0 <= f(x)
                       solver.mkTerm(kinds.Leq, zero, f_y),  # 0 <= f(y)
                       solver.mkTerm(kinds.Leq, summ, one),  # f(x) + f(y) <= 1
                       p_0.notTerm(),                        # not p(0)
                       p_f_y                                 # p(f(y))
                      ])

    solver.checkSatAssuming(solver.mkTrue())
    solver.assertFormula(assertions)
    solver.checkSatAssuming(solver.mkTerm(kinds.Distinct, x, y))
    solver.checkSatAssuming(
        [solver.mkFalse(),
         solver.mkTerm(kinds.Distinct, x, y)])
    with pytest.raises(RuntimeError):
        solver.checkSatAssuming(n)
    with pytest.raises(RuntimeError):
        solver.checkSatAssuming([n, solver.mkTerm(kinds.Distinct, x, y)])
    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.checkSatAssuming(solver.mkTrue())


def test_set_logic(solver):
    solver.setLogic("AUFLIRA")
    with pytest.raises(RuntimeError):
        solver.setLogic("AF_BV")
    solver.assertFormula(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.setLogic("AUFLIRA")


def test_set_option(solver):
    solver.setOption("bv-sat-solver", "minisat")
    with pytest.raises(RuntimeError):
        solver.setOption("bv-sat-solver", "1")
    solver.assertFormula(solver.mkTrue())
    with pytest.raises(RuntimeError):
        solver.setOption("bv-sat-solver", "minisat")


def test_reset_assertions(solver):
    solver.setOption("incremental", "true")

    bvSort = solver.mkBitVectorSort(4)
    one = solver.mkBitVector(4, 1)
    x = solver.mkConst(bvSort, "x")
    ule = solver.mkTerm(kinds.BVUle, x, one)
    srem = solver.mkTerm(kinds.BVSrem, one, x)
    solver.push(4)
    slt = solver.mkTerm(kinds.BVSlt, srem, one)
    solver.resetAssertions()
    solver.checkSatAssuming([slt, ule])


def test_mk_sygus_grammar(solver):
    nullTerm = pycvc5.Term(solver)
    boolTerm = solver.mkBoolean(True)
    boolVar = solver.mkVar(solver.getBooleanSort())
    intVar = solver.mkVar(solver.getIntegerSort())

    solver.mkSygusGrammar([], [intVar])
    solver.mkSygusGrammar([boolVar], [intVar])
    with pytest.raises(RuntimeError):
        solver.mkSygusGrammar([], [])
    with pytest.raises(RuntimeError):
        solver.mkSygusGrammar([], [nullTerm])
    with pytest.raises(RuntimeError):
        solver.mkSygusGrammar([], [boolTerm])
    with pytest.raises(RuntimeError):
        solver.mkSygusGrammar([boolTerm], [intVar])
    slv = pycvc5.Solver()
    boolVar2 = slv.mkVar(slv.getBooleanSort())
    intVar2 = slv.mkVar(slv.getIntegerSort())
    slv.mkSygusGrammar([boolVar2], [intVar2])
    with pytest.raises(RuntimeError):
        slv.mkSygusGrammar([boolVar], [intVar2])
    with pytest.raises(RuntimeError):
        slv.mkSygusGrammar([boolVar2], [intVar])


def test_synth_inv(solver):
    boolean = solver.getBooleanSort()
    integer = solver.getIntegerSort()

    nullTerm = pycvc5.Term(solver)
    x = solver.mkVar(boolean)

    start1 = solver.mkVar(boolean)
    start2 = solver.mkVar(integer)

    g1 = solver.mkSygusGrammar([x], [start1])
    g1.addRule(start1, solver.mkBoolean(False))

    g2 = solver.mkSygusGrammar([x], [start2])
    g2.addRule(start2, solver.mkInteger(0))

    solver.synthInv("", [])
    solver.synthInv("i1", [x])
    solver.synthInv("i2", [x], g1)

    with pytest.raises(RuntimeError):
        solver.synthInv("i3", [nullTerm])
    with pytest.raises(RuntimeError):
        solver.synthInv("i4", [x], g2)


def test_add_sygus_constraint(solver):
    nullTerm = pycvc5.Term(solver)
    boolTerm = solver.mkBoolean(True)
    intTerm = solver.mkInteger(1)

    solver.addSygusConstraint(boolTerm)
    with pytest.raises(RuntimeError):
        solver.addSygusConstraint(nullTerm)
    with pytest.raises(RuntimeError):
        solver.addSygusConstraint(intTerm)

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.addSygusConstraint(boolTerm)


def test_add_sygus_inv_constraint(solver):
    boolean = solver.getBooleanSort()
    real = solver.getRealSort()

    nullTerm = pycvc5.Term(solver)
    intTerm = solver.mkInteger(1)

    inv = solver.declareFun("inv", [real], boolean)
    pre = solver.declareFun("pre", [real], boolean)
    trans = solver.declareFun("trans", [real, real], boolean)
    post = solver.declareFun("post", [real], boolean)

    inv1 = solver.declareFun("inv1", [real], real)

    trans1 = solver.declareFun("trans1", [boolean, real], boolean)
    trans2 = solver.declareFun("trans2", [real, boolean], boolean)
    trans3 = solver.declareFun("trans3", [real, real], real)

    solver.addSygusInvConstraint(inv, pre, trans, post)

    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(nullTerm, pre, trans, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, nullTerm, trans, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, nullTerm, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, trans, nullTerm)

    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(intTerm, pre, trans, post)

    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv1, pre, trans, post)

    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, trans, trans, post)

    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, intTerm, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, pre, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, trans1, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, trans2, post)
    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, trans3, post)

    with pytest.raises(RuntimeError):
        solver.addSygusInvConstraint(inv, pre, trans, trans)
    slv = pycvc5.Solver()
    boolean2 = slv.getBooleanSort()
    real2 = slv.getRealSort()
    inv22 = slv.declareFun("inv", [real2], boolean2)
    pre22 = slv.declareFun("pre", [real2], boolean2)
    trans22 = slv.declareFun("trans", [real2, real2], boolean2)
    post22 = slv.declareFun("post", [real2], boolean2)
    slv.addSygusInvConstraint(inv22, pre22, trans22, post22)
    with pytest.raises(RuntimeError):
        slv.addSygusInvConstraint(inv, pre22, trans22, post22)
    with pytest.raises(RuntimeError):
        slv.addSygusInvConstraint(inv22, pre, trans22, post22)
    with pytest.raises(RuntimeError):
        slv.addSygusInvConstraint(inv22, pre22, trans, post22)
    with pytest.raises(RuntimeError):
        slv.addSygusInvConstraint(inv22, pre22, trans22, post)


def test_get_synth_solution(solver):
    solver.setOption("lang", "sygus2")
    solver.setOption("incremental", "false")

    nullTerm = pycvc5.Term(solver)
    x = solver.mkBoolean(False)
    f = solver.synthFun("f", [], solver.getBooleanSort())

    with pytest.raises(RuntimeError):
        solver.getSynthSolution(f)

    solver.checkSynth()

    solver.getSynthSolution(f)
    solver.getSynthSolution(f)

    with pytest.raises(RuntimeError):
        solver.getSynthSolution(nullTerm)
    with pytest.raises(RuntimeError):
        solver.getSynthSolution(x)

    slv = pycvc5.Solver()
    with pytest.raises(RuntimeError):
        slv.getSynthSolution(f)









######################################################################
######################################################################
#                               MISSING TESTS
######################################################################
######################################################################









TEST_F(TestApiBlackSolver, addSygusAssume)
{
  Term nullTerm;
  Term boolTerm = d_solver.mkBoolean(false);
  Term intTerm = d_solver.mkInteger(1);

  ASSERT_NO_THROW(d_solver.addSygusAssume(boolTerm));
  ASSERT_THROW(d_solver.addSygusAssume(nullTerm), CVC5ApiException);
  ASSERT_THROW(d_solver.addSygusAssume(intTerm), CVC5ApiException);

  Solver slv;
  ASSERT_THROW(slv.addSygusAssume(boolTerm), CVC5ApiException);
}


TEST_F(TestApiBlackSolver, blockModel1)
{
  d_solver.setOption("produce-models", "true");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_THROW(d_solver.blockModel(), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, blockModel2)
{
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_THROW(d_solver.blockModel(), CVC5ApiException);
}





TEST_F(TestApiBlackSolver, blockModel3)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  ASSERT_THROW(d_solver.blockModel(), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, blockModel4)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.blockModel());
}




TEST_F(TestApiBlackSolver, blockModelValues1)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_THROW(d_solver.blockModelValues({}), CVC5ApiException);
  ASSERT_THROW(d_solver.blockModelValues({Term()}), CVC5ApiException);
  ASSERT_THROW(d_solver.blockModelValues({Solver().mkBoolean(false)}),
               CVC5ApiException);
}




TEST_F(TestApiBlackSolver, blockModelValues2)
{
  d_solver.setOption("produce-models", "true");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_THROW(d_solver.blockModelValues({x}), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, blockModelValues3)
{
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_THROW(d_solver.blockModelValues({x}), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, blockModelValues4)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  ASSERT_THROW(d_solver.blockModelValues({x}), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, blockModelValues5)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("block-models", "literals");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x));
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.blockModelValues({x}));
}




TEST_F(TestApiBlackSolver, declareDatatype)
{
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  std::vector<DatatypeConstructorDecl> ctors1 = {nil};
  ASSERT_NO_THROW(d_solver.declareDatatype(std::string("a"), ctors1));
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil2 = d_solver.mkDatatypeConstructorDecl("nil");
  std::vector<DatatypeConstructorDecl> ctors2 = {cons, nil2};
  ASSERT_NO_THROW(d_solver.declareDatatype(std::string("b"), ctors2));
  DatatypeConstructorDecl cons2 = d_solver.mkDatatypeConstructorDecl("cons");
  DatatypeConstructorDecl nil3 = d_solver.mkDatatypeConstructorDecl("nil");
  std::vector<DatatypeConstructorDecl> ctors3 = {cons2, nil3};
  ASSERT_NO_THROW(d_solver.declareDatatype(std::string(""), ctors3));
  std::vector<DatatypeConstructorDecl> ctors4;
  ASSERT_THROW(d_solver.declareDatatype(std::string("c"), ctors4),
               CVC5ApiException);
  ASSERT_THROW(d_solver.declareDatatype(std::string(""), ctors4),
               CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.declareDatatype(std::string("a"), ctors1), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, declarePool)
{
  Sort intSort = d_solver.getIntegerSort();
  Sort setSort = d_solver.mkSetSort(intSort);
  Term zero = d_solver.mkInteger(0);
  Term x = d_solver.mkConst(intSort, "x");
  Term y = d_solver.mkConst(intSort, "y");
  // declare a pool with initial value { 0, x, y }
  Term p = d_solver.declarePool("p", intSort, {zero, x, y});
  // pool should have the same sort
  ASSERT_TRUE(p.getSort() == setSort);
  // cannot pass null sort
  Sort nullSort;
  ASSERT_THROW(d_solver.declarePool("i", nullSort, {}), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, declareSepHeap)
{
  d_solver.setLogic("ALL");
  Sort integer = d_solver.getIntegerSort();
  ASSERT_NO_THROW(d_solver.declareSepHeap(integer, integer));
  // cannot declare separation logic heap more than once
  ASSERT_THROW(d_solver.declareSepHeap(integer, integer), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, defineFunGlobal)
{
  Sort bSort = d_solver.getBooleanSort();

  Term bTrue = d_solver.mkBoolean(true);
  // (define-fun f () Bool true)
  Term f = d_solver.defineFun("f", {}, bSort, bTrue, true);
  Term b = d_solver.mkVar(bSort, "b");
  // (define-fun g (b Bool) Bool b)
  Term g = d_solver.defineFun("g", {b}, bSort, b, true);

  // (assert (or (not f) (not (g true))))
  d_solver.assertFormula(d_solver.mkTerm(
      OR, f.notTerm(), d_solver.mkTerm(APPLY_UF, g, bTrue).notTerm()));
  ASSERT_TRUE(d_solver.checkSat().isUnsat());
  d_solver.resetAssertions();
  // (assert (or (not f) (not (g true))))
  d_solver.assertFormula(d_solver.mkTerm(
      OR, f.notTerm(), d_solver.mkTerm(APPLY_UF, g, bTrue).notTerm()));
  ASSERT_TRUE(d_solver.checkSat().isUnsat());
}




TEST_F(TestApiBlackSolver, defineFunRecGlobal)
{
  Sort bSort = d_solver.getBooleanSort();
  Sort fSort = d_solver.mkFunctionSort(bSort, bSort);

  d_solver.push();
  Term bTrue = d_solver.mkBoolean(true);
  // (define-fun f () Bool true)
  Term f = d_solver.defineFunRec("f", {}, bSort, bTrue, true);
  Term b = d_solver.mkVar(bSort, "b");
  Term gSym = d_solver.mkConst(fSort, "g");
  // (define-fun g (b Bool) Bool b)
  Term g = d_solver.defineFunRec(gSym, {b}, b, true);

  // (assert (or (not f) (not (g true))))
  d_solver.assertFormula(d_solver.mkTerm(
      OR, f.notTerm(), d_solver.mkTerm(APPLY_UF, g, bTrue).notTerm()));
  ASSERT_TRUE(d_solver.checkSat().isUnsat());
  d_solver.pop();
  // (assert (or (not f) (not (g true))))
  d_solver.assertFormula(d_solver.mkTerm(
      OR, f.notTerm(), d_solver.mkTerm(APPLY_UF, g, bTrue).notTerm()));
  ASSERT_TRUE(d_solver.checkSat().isUnsat());
}




TEST_F(TestApiBlackSolver, defineFunsRec)
{
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort1 = d_solver.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver.mkFunctionSort(uSort, d_solver.getIntegerSort());
  Term b1 = d_solver.mkVar(bvSort, "b1");
  Term b11 = d_solver.mkVar(bvSort, "b1");
  Term b2 = d_solver.mkVar(d_solver.getIntegerSort(), "b2");
  Term b3 = d_solver.mkVar(funSort2, "b3");
  Term b4 = d_solver.mkVar(uSort, "b4");
  Term v1 = d_solver.mkConst(bvSort, "v1");
  Term v2 = d_solver.mkConst(d_solver.getIntegerSort(), "v2");
  Term v3 = d_solver.mkConst(funSort2, "v3");
  Term v4 = d_solver.mkConst(uSort, "v4");
  Term f1 = d_solver.mkConst(funSort1, "f1");
  Term f2 = d_solver.mkConst(funSort2, "f2");
  Term f3 = d_solver.mkConst(bvSort, "f3");
  ASSERT_NO_THROW(
      d_solver.defineFunsRec({f1, f2}, {{b1, b11}, {b4}}, {v1, v2}));
  ASSERT_THROW(d_solver.defineFunsRec({f1, f2}, {{v1, b11}, {b4}}, {v1, v2}),
               CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunsRec({f1, f3}, {{b1, b11}, {b4}}, {v1, v2}),
               CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunsRec({f1, f2}, {{b1}, {b4}}, {v1, v2}),
               CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunsRec({f1, f2}, {{b1, b2}, {b4}}, {v1, v2}),
               CVC5ApiException);
  ASSERT_THROW(d_solver.defineFunsRec({f1, f2}, {{b1, b11}, {b4}}, {v1, v4}),
               CVC5ApiException);

  Solver slv;
  Sort uSort2 = slv.mkUninterpretedSort("u");
  Sort bvSort2 = slv.mkBitVectorSort(32);
  Sort funSort12 = slv.mkFunctionSort({bvSort2, bvSort2}, bvSort2);
  Sort funSort22 = slv.mkFunctionSort(uSort2, slv.getIntegerSort());
  Term b12 = slv.mkVar(bvSort2, "b1");
  Term b112 = slv.mkVar(bvSort2, "b1");
  Term b42 = slv.mkVar(uSort2, "b4");
  Term v12 = slv.mkConst(bvSort2, "v1");
  Term v22 = slv.mkConst(slv.getIntegerSort(), "v2");
  Term f12 = slv.mkConst(funSort12, "f1");
  Term f22 = slv.mkConst(funSort22, "f2");
  ASSERT_NO_THROW(
      slv.defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v12, v22}));
  ASSERT_THROW(slv.defineFunsRec({f1, f22}, {{b12, b112}, {b42}}, {v12, v22}),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f2}, {{b12, b112}, {b42}}, {v12, v22}),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b1, b112}, {b42}}, {v12, v22}),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b12, b11}, {b42}}, {v12, v22}),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b12, b112}, {b4}}, {v12, v22}),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v1, v22}),
               CVC5ApiException);
  ASSERT_THROW(slv.defineFunsRec({f12, f22}, {{b12, b112}, {b42}}, {v12, v2}),
               CVC5ApiException);
}




TEST_F(TestApiBlackSolver, defineFunsRecGlobal)
{
  Sort bSort = d_solver.getBooleanSort();
  Sort fSort = d_solver.mkFunctionSort(bSort, bSort);

  d_solver.push();
  Term bTrue = d_solver.mkBoolean(true);
  Term b = d_solver.mkVar(bSort, "b");
  Term gSym = d_solver.mkConst(fSort, "g");
  // (define-funs-rec ((g ((b Bool)) Bool)) (b))
  d_solver.defineFunsRec({gSym}, {{b}}, {b}, true);

  // (assert (not (g true)))
  d_solver.assertFormula(d_solver.mkTerm(APPLY_UF, gSym, bTrue).notTerm());
  ASSERT_TRUE(d_solver.checkSat().isUnsat());
  d_solver.pop();
  // (assert (not (g true)))
  d_solver.assertFormula(d_solver.mkTerm(APPLY_UF, gSym, bTrue).notTerm());
  ASSERT_TRUE(d_solver.checkSat().isUnsat());
}




TEST_F(TestApiBlackSolver, defineFunsRecWrongLogic)
{
  d_solver.setLogic("QF_BV");
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort bvSort = d_solver.mkBitVectorSort(32);
  Sort funSort1 = d_solver.mkFunctionSort({bvSort, bvSort}, bvSort);
  Sort funSort2 = d_solver.mkFunctionSort(uSort, d_solver.getIntegerSort());
  Term b = d_solver.mkVar(bvSort, "b");
  Term u = d_solver.mkVar(uSort, "u");
  Term v1 = d_solver.mkConst(bvSort, "v1");
  Term v2 = d_solver.mkConst(d_solver.getIntegerSort(), "v2");
  Term f1 = d_solver.mkConst(funSort1, "f1");
  Term f2 = d_solver.mkConst(funSort2, "f2");
  ASSERT_THROW(d_solver.defineFunsRec({f1, f2}, {{b, b}, {u}}, {v1, v2}),
               CVC5ApiException);
}




TEST_F(TestApiBlackSolver, defineSort)
{
  Sort sortVar0 = d_solver.mkParamSort("T0");
  Sort sortVar1 = d_solver.mkParamSort("T1");
  Sort intSort = d_solver.getIntegerSort();
  Sort realSort = d_solver.getRealSort();
  Sort arraySort0 = d_solver.mkArraySort(sortVar0, sortVar0);
  Sort arraySort1 = d_solver.mkArraySort(sortVar0, sortVar1);
  // Now create instantiations of the defined sorts
  ASSERT_NO_THROW(arraySort0.substitute(sortVar0, intSort));
  ASSERT_NO_THROW(
      arraySort1.substitute({sortVar0, sortVar1}, {intSort, realSort}));
}




TEST_F(TestApiBlackSolver, getAbduct)
{
  d_solver.setLogic("QF_LIA");
  d_solver.setOption("produce-abducts", "true");
  d_solver.setOption("incremental", "false");

  Sort intSort = d_solver.getIntegerSort();
  Term zero = d_solver.mkInteger(0);
  Term x = d_solver.mkConst(intSort, "x");
  Term y = d_solver.mkConst(intSort, "y");

  // Assumptions for abduction: x > 0
  d_solver.assertFormula(d_solver.mkTerm(GT, x, zero));
  // Conjecture for abduction: y > 0
  Term conj = d_solver.mkTerm(GT, y, zero);
  Term output;
  // Call the abduction api, while the resulting abduct is the output
  ASSERT_TRUE(d_solver.getAbduct(conj, output));
  // We expect the resulting output to be a boolean formula
  ASSERT_TRUE(!output.isNull() && output.getSort().isBoolean());

  // try with a grammar, a simple grammar admitting true
  Sort boolean = d_solver.getBooleanSort();
  Term truen = d_solver.mkBoolean(true);
  Term start = d_solver.mkVar(boolean);
  Term output2;
  Grammar g = d_solver.mkSygusGrammar({}, {start});
  Term conj2 = d_solver.mkTerm(GT, x, zero);
  ASSERT_NO_THROW(g.addRule(start, truen));
  // Call the abduction api, while the resulting abduct is the output
  ASSERT_TRUE(d_solver.getAbduct(conj2, g, output2));
  // abduct must be true
  ASSERT_EQ(output2, truen);
}




TEST_F(TestApiBlackSolver, getAbduct2)
{
  d_solver.setLogic("QF_LIA");
  d_solver.setOption("incremental", "false");
  Sort intSort = d_solver.getIntegerSort();
  Term zero = d_solver.mkInteger(0);
  Term x = d_solver.mkConst(intSort, "x");
  Term y = d_solver.mkConst(intSort, "y");
  // Assumptions for abduction: x > 0
  d_solver.assertFormula(d_solver.mkTerm(GT, x, zero));
  // Conjecture for abduction: y > 0
  Term conj = d_solver.mkTerm(GT, y, zero);
  Term output;
  // Fails due to option not set
  ASSERT_THROW(d_solver.getAbduct(conj, output), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getDifficulty)
{
  d_solver.setOption("produce-difficulty", "true");
  // cannot ask before a check sat
  ASSERT_THROW(d_solver.getDifficulty(), CVC5ApiException);
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.getDifficulty());
}




TEST_F(TestApiBlackSolver, getDifficulty2)
{
  d_solver.checkSat();
  // option is not set
  ASSERT_THROW(d_solver.getDifficulty(), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getDifficulty3)
{
  d_solver.setOption("produce-difficulty", "true");
  Sort intSort = d_solver.getIntegerSort();
  Term x = d_solver.mkConst(intSort, "x");
  Term zero = d_solver.mkInteger(0);
  Term ten = d_solver.mkInteger(10);
  Term f0 = d_solver.mkTerm(GEQ, x, ten);
  Term f1 = d_solver.mkTerm(GEQ, zero, x);
  d_solver.checkSat();
  std::map<Term, Term> dmap;
  ASSERT_NO_THROW(dmap = d_solver.getDifficulty());
  // difficulty should map assertions to integer values
  for (const std::pair<const Term, Term>& t : dmap)
  {
    ASSERT_TRUE(t.first == f0 || t.first == f1);
    ASSERT_TRUE(t.second.getKind() == CONST_RATIONAL);
  }
}




TEST_F(TestApiBlackSolver, getInterpolant)
{
  d_solver.setLogic("QF_LIA");
  d_solver.setOption("produce-interpols", "default");
  d_solver.setOption("incremental", "false");

  Sort intSort = d_solver.getIntegerSort();
  Term zero = d_solver.mkInteger(0);
  Term x = d_solver.mkConst(intSort, "x");
  Term y = d_solver.mkConst(intSort, "y");
  Term z = d_solver.mkConst(intSort, "z");

  // Assumptions for interpolation: x + y > 0 /\ x < 0
  d_solver.assertFormula(
      d_solver.mkTerm(GT, d_solver.mkTerm(PLUS, x, y), zero));
  d_solver.assertFormula(d_solver.mkTerm(LT, x, zero));
  // Conjecture for interpolation: y + z > 0 \/ z < 0
  Term conj =
      d_solver.mkTerm(OR,
                      d_solver.mkTerm(GT, d_solver.mkTerm(PLUS, y, z), zero),
                      d_solver.mkTerm(LT, z, zero));
  Term output;
  // Call the interpolation api, while the resulting interpolant is the output
  d_solver.getInterpolant(conj, output);

  // We expect the resulting output to be a boolean formula
  ASSERT_TRUE(output.getSort().isBoolean());
}




TEST_F(TestApiBlackSolver, getModelDomainElements)
{
  d_solver.setOption("produce-models", "true");
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort intSort = d_solver.getIntegerSort();
  Term x = d_solver.mkConst(uSort, "x");
  Term y = d_solver.mkConst(uSort, "y");
  Term z = d_solver.mkConst(uSort, "z");
  Term f = d_solver.mkTerm(DISTINCT, x, y, z);
  d_solver.assertFormula(f);
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.getModelDomainElements(uSort));
  ASSERT_TRUE(d_solver.getModelDomainElements(uSort).size() >= 3);
  ASSERT_THROW(d_solver.getModelDomainElements(intSort), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getModel2)
{
  d_solver.setOption("produce-models", "true");
  std::vector<Sort> sorts;
  std::vector<Term> terms;
  ASSERT_THROW(d_solver.getModel(sorts, terms), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getModel3)
{
  d_solver.setOption("produce-models", "true");
  std::vector<Sort> sorts;
  std::vector<Term> terms;
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.getModel(sorts, terms));
  Sort integer = d_solver.getIntegerSort();
  sorts.push_back(integer);
  ASSERT_THROW(d_solver.getModel(sorts, terms), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getModelDomainElements)
{
  d_solver.setOption("produce-models", "true");
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Sort intSort = d_solver.getIntegerSort();
  Term x = d_solver.mkConst(uSort, "x");
  Term y = d_solver.mkConst(uSort, "y");
  Term z = d_solver.mkConst(uSort, "z");
  Term f = d_solver.mkTerm(DISTINCT, x, y, z);
  d_solver.assertFormula(f);
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.getModelDomainElements(uSort));
  ASSERT_TRUE(d_solver.getModelDomainElements(uSort).size() >= 3);
  ASSERT_THROW(d_solver.getModelDomainElements(intSort), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getModelDomainElements2)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("finite-model-find", "true");
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkVar(uSort, "x");
  Term y = d_solver.mkVar(uSort, "y");
  Term eq = d_solver.mkTerm(EQUAL, x, y);
  Term bvl = d_solver.mkTerm(VARIABLE_LIST, x, y);
  Term f = d_solver.mkTerm(FORALL, bvl, eq);
  d_solver.assertFormula(f);
  d_solver.checkSat();
  ASSERT_NO_THROW(d_solver.getModelDomainElements(uSort));
  // a model for the above must interpret u as size 1
  ASSERT_TRUE(d_solver.getModelDomainElements(uSort).size() == 1);
}




TEST_F(TestApiBlackSolver, getOptionInfo)
{
  {
    EXPECT_THROW(d_solver.getOptionInfo("asdf-invalid"), CVC5ApiException);
  }
  {
    api::OptionInfo info = d_solver.getOptionInfo("verbose");
    EXPECT_EQ("verbose", info.name);
    EXPECT_EQ(std::vector<std::string>{}, info.aliases);
    EXPECT_TRUE(std::holds_alternative<OptionInfo::VoidInfo>(info.valueInfo));
  }
  {
    // int64 type with default
    api::OptionInfo info = d_solver.getOptionInfo("verbosity");
    EXPECT_EQ("verbosity", info.name);
    EXPECT_EQ(std::vector<std::string>{}, info.aliases);
    EXPECT_TRUE(std::holds_alternative<OptionInfo::NumberInfo<int64_t>>(
        info.valueInfo));
    auto numInfo = std::get<OptionInfo::NumberInfo<int64_t>>(info.valueInfo);
    EXPECT_EQ(0, numInfo.defaultValue);
    EXPECT_EQ(0, numInfo.currentValue);
    EXPECT_FALSE(numInfo.minimum || numInfo.maximum);
    ASSERT_EQ(info.intValue(), 0);
  }
  {
    auto info = d_solver.getOptionInfo("random-freq");
    ASSERT_EQ(info.name, "random-freq");
    ASSERT_EQ(info.aliases, std::vector<std::string>{"random-frequency"});
    ASSERT_TRUE(std::holds_alternative<api::OptionInfo::NumberInfo<double>>(
        info.valueInfo));
    auto ni = std::get<api::OptionInfo::NumberInfo<double>>(info.valueInfo);
    ASSERT_EQ(ni.currentValue, 0.0);
    ASSERT_EQ(ni.defaultValue, 0.0);
    ASSERT_TRUE(ni.minimum && ni.maximum);
    ASSERT_EQ(*ni.minimum, 0.0);
    ASSERT_EQ(*ni.maximum, 1.0);
    ASSERT_EQ(info.doubleValue(), 0.0);
  }
  {
    // mode option
    api::OptionInfo info = d_solver.getOptionInfo("output");
    EXPECT_EQ("output", info.name);
    EXPECT_EQ(std::vector<std::string>{}, info.aliases);
    EXPECT_TRUE(std::holds_alternative<OptionInfo::ModeInfo>(info.valueInfo));
    auto modeInfo = std::get<OptionInfo::ModeInfo>(info.valueInfo);
    EXPECT_EQ("none", modeInfo.defaultValue);
    EXPECT_EQ("none", modeInfo.currentValue);
    EXPECT_TRUE(std::find(modeInfo.modes.begin(), modeInfo.modes.end(), "none")
                != modeInfo.modes.end());
  }
}




TEST_F(TestApiBlackSolver, getOptionNames)
{
  std::vector<std::string> names = d_solver.getOptionNames();
  ASSERT_TRUE(names.size() > 100);
  ASSERT_NE(std::find(names.begin(), names.end(), "verbose"), names.end());
  ASSERT_EQ(std::find(names.begin(), names.end(), "foobar"), names.end());
}




TEST_F(TestApiBlackSolver, getQuantifierElimination)
{
  Term x = d_solver.mkVar(d_solver.getBooleanSort(), "x");
  Term forall =
      d_solver.mkTerm(FORALL,
                      d_solver.mkTerm(VARIABLE_LIST, x),
                      d_solver.mkTerm(OR, x, d_solver.mkTerm(NOT, x)));
  ASSERT_THROW(d_solver.getQuantifierElimination(Term()), CVC5ApiException);
  ASSERT_THROW(d_solver.getQuantifierElimination(Solver().mkBoolean(false)),
               CVC5ApiException);
  ASSERT_NO_THROW(d_solver.getQuantifierElimination(forall));
}




TEST_F(TestApiBlackSolver, getQuantifierEliminationDisjunct)
{
  Term x = d_solver.mkVar(d_solver.getBooleanSort(), "x");
  Term forall =
      d_solver.mkTerm(FORALL,
                      d_solver.mkTerm(VARIABLE_LIST, x),
                      d_solver.mkTerm(OR, x, d_solver.mkTerm(NOT, x)));
  ASSERT_THROW(d_solver.getQuantifierEliminationDisjunct(Term()),
               CVC5ApiException);
  ASSERT_THROW(
      d_solver.getQuantifierEliminationDisjunct(Solver().mkBoolean(false)),
      CVC5ApiException);
  ASSERT_NO_THROW(d_solver.getQuantifierEliminationDisjunct(forall));
}




TEST_F(TestApiBlackSolver, getSynthSolutions)
{
  d_solver.setOption("lang", "sygus2");
  d_solver.setOption("incremental", "false");

  Term nullTerm;
  Term x = d_solver.mkBoolean(false);
  Term f = d_solver.synthFun("f", {}, d_solver.getBooleanSort());

  ASSERT_THROW(d_solver.getSynthSolutions({}), CVC5ApiException);
  ASSERT_THROW(d_solver.getSynthSolutions({f}), CVC5ApiException);

  d_solver.checkSynth();

  ASSERT_NO_THROW(d_solver.getSynthSolutions({f}));
  ASSERT_NO_THROW(d_solver.getSynthSolutions({f, f}));

  ASSERT_THROW(d_solver.getSynthSolutions({}), CVC5ApiException);
  ASSERT_THROW(d_solver.getSynthSolutions({nullTerm}), CVC5ApiException);
  ASSERT_THROW(d_solver.getSynthSolutions({x}), CVC5ApiException);

  Solver slv;
  ASSERT_THROW(slv.getSynthSolutions({x}), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getValueSepHeap1)
{
  d_solver.setLogic("QF_BV");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  ASSERT_THROW(d_solver.getValueSepHeap(), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getValueSepHeap2)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "false");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_THROW(d_solver.getValueSepHeap(), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getValueSepHeap3)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkFalse();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getValueSepHeap(), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getValueSepHeap4)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getValueSepHeap(), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getValueSepHeap5)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_NO_THROW(d_solver.getValueSepHeap());
}




TEST_F(TestApiBlackSolver, getValueSepNil1)
{
  d_solver.setLogic("QF_BV");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  ASSERT_THROW(d_solver.getValueSepNil(), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getValueSepNil2)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "false");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_THROW(d_solver.getValueSepNil(), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getValueSepNil3)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkFalse();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getValueSepNil(), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getValueSepNil4)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  Term t = d_solver.mkTrue();
  d_solver.assertFormula(t);
  d_solver.checkSat();
  ASSERT_THROW(d_solver.getValueSepNil(), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, getValueSepNil5)
{
  d_solver.setLogic("ALL");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("produce-models", "true");
  checkSimpleSeparationConstraints(&d_solver);
  ASSERT_NO_THROW(d_solver.getValueSepNil());
}




TEST_F(TestApiBlackSolver, isModelCoreSymbol)
{
  d_solver.setOption("produce-models", "true");
  d_solver.setOption("model-cores", "simple");
  Sort uSort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkConst(uSort, "x");
  Term y = d_solver.mkConst(uSort, "y");
  Term z = d_solver.mkConst(uSort, "z");
  Term zero = d_solver.mkInteger(0);
  Term f = d_solver.mkTerm(NOT, d_solver.mkTerm(EQUAL, x, y));
  d_solver.assertFormula(f);
  d_solver.checkSat();
  ASSERT_TRUE(d_solver.isModelCoreSymbol(x));
  ASSERT_TRUE(d_solver.isModelCoreSymbol(y));
  ASSERT_FALSE(d_solver.isModelCoreSymbol(z));
  ASSERT_THROW(d_solver.isModelCoreSymbol(zero), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, issue5893)
{
  Solver slv;
  Sort bvsort4 = d_solver.mkBitVectorSort(4);
  Sort bvsort8 = d_solver.mkBitVectorSort(8);
  Sort arrsort = d_solver.mkArraySort(bvsort4, bvsort8);
  Term arr = d_solver.mkConst(arrsort, "arr");
  Term idx = d_solver.mkConst(bvsort4, "idx");
  Term ten = d_solver.mkBitVector(8, "10", 10);
  Term sel = d_solver.mkTerm(SELECT, arr, idx);
  Term distinct = d_solver.mkTerm(DISTINCT, sel, ten);
  ASSERT_NO_FATAL_FAILURE(distinct.getOp());
}




TEST_F(TestApiBlackSolver, issue7000)
{
  Sort s1 = d_solver.getIntegerSort();
  Sort s2 = d_solver.mkFunctionSort(s1, s1);
  Sort s3 = d_solver.getRealSort();
  Term t4 = d_solver.mkPi();
  Term t7 = d_solver.mkConst(s3, "_x5");
  Term t37 = d_solver.mkConst(s2, "_x32");
  Term t59 = d_solver.mkConst(s2, "_x51");
  Term t72 = d_solver.mkTerm(EQUAL, t37, t59);
  Term t74 = d_solver.mkTerm(GT, t4, t7);
  // throws logic exception since logic is not higher order by default
  ASSERT_THROW(d_solver.checkEntailed({t72, t74, t72, t72}), CVC5ApiException);
}






















TEST_F(TestApiBlackSolver, mkSygusVar)
{
  Sort boolSort = d_solver.getBooleanSort();
  Sort intSort = d_solver.getIntegerSort();
  Sort funSort = d_solver.mkFunctionSort(intSort, boolSort);

  ASSERT_NO_THROW(d_solver.mkSygusVar(boolSort));
  ASSERT_NO_THROW(d_solver.mkSygusVar(funSort));
  ASSERT_NO_THROW(d_solver.mkSygusVar(boolSort, std::string("b")));
  ASSERT_NO_THROW(d_solver.mkSygusVar(funSort, ""));
  ASSERT_THROW(d_solver.mkSygusVar(Sort()), CVC5ApiException);
  ASSERT_THROW(d_solver.mkSygusVar(d_solver.getNullSort(), "a"),
               CVC5ApiException);
  Solver slv;
  ASSERT_THROW(slv.mkSygusVar(boolSort), CVC5ApiException);
}




TEST_F(TestApiBlackSolver, Output)
{
  ASSERT_THROW(d_solver.isOutputOn("foo-invalid"), CVC5ApiException);
  ASSERT_THROW(d_solver.getOutput("foo-invalid"), CVC5ApiException);
  ASSERT_FALSE(d_solver.isOutputOn("inst"));
  ASSERT_EQ(cvc5::null_os.rdbuf(), d_solver.getOutput("inst").rdbuf());
  d_solver.setOption("output", "inst");
  ASSERT_TRUE(d_solver.isOutputOn("inst"));
  ASSERT_NE(cvc5::null_os.rdbuf(), d_solver.getOutput("inst").rdbuf());
}





TEST_F(TestApiBlackSolver, synthFun)
{
  Sort null = d_solver.getNullSort();
  Sort boolean = d_solver.getBooleanSort();
  Sort integer = d_solver.getIntegerSort();

  Term nullTerm;
  Term x = d_solver.mkVar(boolean);

  Term start1 = d_solver.mkVar(boolean);
  Term start2 = d_solver.mkVar(integer);

  Grammar g1 = d_solver.mkSygusGrammar({x}, {start1});
  g1.addRule(start1, d_solver.mkBoolean(false));

  Grammar g2 = d_solver.mkSygusGrammar({x}, {start2});
  g2.addRule(start2, d_solver.mkInteger(0));

  ASSERT_NO_THROW(d_solver.synthFun("", {}, boolean));
  ASSERT_NO_THROW(d_solver.synthFun("f1", {x}, boolean));
  ASSERT_NO_THROW(d_solver.synthFun("f2", {x}, boolean, g1));

  ASSERT_THROW(d_solver.synthFun("f3", {nullTerm}, boolean), CVC5ApiException);
  ASSERT_THROW(d_solver.synthFun("f4", {}, null), CVC5ApiException);
  ASSERT_THROW(d_solver.synthFun("f6", {x}, boolean, g2), CVC5ApiException);
  Solver slv;
  Term x2 = slv.mkVar(slv.getBooleanSort());
  ASSERT_NO_THROW(slv.synthFun("f1", {x2}, slv.getBooleanSort()));
  ASSERT_THROW(slv.synthFun("", {}, d_solver.getBooleanSort()),
               CVC5ApiException);
  ASSERT_THROW(slv.synthFun("f1", {x}, d_solver.getBooleanSort()),
               CVC5ApiException);
}




TEST_F(TestApiBlackSolver, tupleProject)
{
  std::vector<Sort> sorts = {d_solver.getBooleanSort(),
                             d_solver.getIntegerSort(),
                             d_solver.getStringSort(),
                             d_solver.mkSetSort(d_solver.getStringSort())};
  std::vector<Term> elements = {
      d_solver.mkBoolean(true),
      d_solver.mkInteger(3),
      d_solver.mkString("C"),
      d_solver.mkTerm(SET_SINGLETON, d_solver.mkString("Z"))};

  Term tuple = d_solver.mkTuple(sorts, elements);

  std::vector<uint32_t> indices1 = {};
  std::vector<uint32_t> indices2 = {0};
  std::vector<uint32_t> indices3 = {0, 1};
  std::vector<uint32_t> indices4 = {0, 0, 2, 2, 3, 3, 0};
  std::vector<uint32_t> indices5 = {4};
  std::vector<uint32_t> indices6 = {0, 4};

  ASSERT_NO_THROW(
      d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices1), tuple));
  ASSERT_NO_THROW(
      d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices2), tuple));
  ASSERT_NO_THROW(
      d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices3), tuple));
  ASSERT_NO_THROW(
      d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices4), tuple));

  ASSERT_THROW(d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices5), tuple),
               CVC5ApiException);
  ASSERT_THROW(d_solver.mkTerm(d_solver.mkOp(TUPLE_PROJECT, indices6), tuple),
               CVC5ApiException);

  std::vector<uint32_t> indices = {0, 3, 2, 0, 1, 2};

  Op op = d_solver.mkOp(TUPLE_PROJECT, indices);
  Term projection = d_solver.mkTerm(op, tuple);

  Datatype datatype = tuple.getSort().getDatatype();
  DatatypeConstructor constructor = datatype[0];

  for (size_t i = 0; i < indices.size(); i++)
  {
    Term selectorTerm = constructor[indices[i]].getSelectorTerm();
    Term selectedTerm = d_solver.mkTerm(APPLY_SELECTOR, selectorTerm, tuple);
    Term simplifiedTerm = d_solver.simplify(selectedTerm);
    ASSERT_EQ(elements[indices[i]], simplifiedTerm);
  }

  ASSERT_EQ(
      "((_ tuple_project 0 3 2 0 1 2) (tuple true 3 \"C\" (set.singleton "
      "\"Z\")))",
      projection.toString());
}


