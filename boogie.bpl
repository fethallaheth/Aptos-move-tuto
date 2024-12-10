
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

datatype Vec<T> {
    Vec(v: [int]T, l: int)
}

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := v->l;
    Vec(v->v[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v->v[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    v->l
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    v->l == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := v->l - 1;
    Vec(v->v[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := v->l - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v->v[j] else v->v[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := v1->l, v1->v, v2->l, v2->v;
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := v->l;
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v->v[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v->v;
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v->v[i := elem], v->l)
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v->v;
    Vec(m[i := m[j]][j := m[i]], v->l))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := v->l;
    (exists i: int :: InRangeVec(v, i) && v->v[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

datatype Multiset<T> {
    Multiset(v: [T]int, l: int)
}

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    s->l
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := s->l;
    (var cnt := s->v[v];
    Multiset(s->v[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := s1->l;
    (var len2 := s2->l;
    Multiset((lambda v:T :: s1->v[v]-s2->v[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (s->l == 0) &&
    (forall v: T :: s->v[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (s1->l <= s2->l) &&
    (forall v: T :: s1->v[v] <= s2->v[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    s->v[v] > 0
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Theory for tables.

// v is the SMT array holding the key-value assignment. e is an array which
// independently determines whether a key is valid or not. l is the length.
//
// Note that even though the program cannot reflect over existence of a key,
// we want the specification to be able to do this, so it can express
// verification conditions like "key has been inserted".
datatype Table <K, V> {
    Table(v: [K]V, e: [K]bool, l: int)
}

// Functions for default SMT arrays. For the table values, we don't care and
// use an uninterpreted function.
function DefaultTableArray<K, V>(): [K]V;
function DefaultTableKeyExistsArray<K>(): [K]bool;
axiom DefaultTableKeyExistsArray() == (lambda i: int :: false);

function {:inline} EmptyTable<K, V>(): Table K V {
    Table(DefaultTableArray(), DefaultTableKeyExistsArray(), 0)
}

function {:inline} GetTable<K,V>(t: Table K V, k: K): V {
    // Notice we do not check whether key is in the table. The result is undetermined if it is not.
    t->v[k]
}

function {:inline} LenTable<K,V>(t: Table K V): int {
    t->l
}


function {:inline} ContainsTable<K,V>(t: Table K V, k: K): bool {
    t->e[k]
}

function {:inline} UpdateTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    Table(t->v[k := v], t->e, t->l)
}

function {:inline} AddTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    // This function has an undetermined result if the key is already in the table
    // (all specification functions have this "partial definiteness" behavior). Thus we can
    // just increment the length.
    Table(t->v[k := v], t->e[k := true], t->l + 1)
}

function {:inline} RemoveTable<K,V>(t: Table K V, k: K): Table K V {
    // Similar as above, we only need to consider the case where the key is in the table.
    Table(t->v, t->e[k := false], t->l - 1)
}

axiom {:ctor "Table"} (forall<K,V> t: Table K V :: {LenTable(t)}
    (exists k: K :: {ContainsTable(t, k)} ContainsTable(t, k)) ==> LenTable(t) >= 1
);
// TODO: we might want to encoder a stronger property that the length of table
// must be more than N given a set of N items. Currently we don't see a need here
// and the above axiom seems to be sufficient.
// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

// ==================================================================================
// Native object::exists_at

// ==================================================================================
// Intrinsic implementation of aggregator and aggregator factory

datatype $1_aggregator_Aggregator {
    $1_aggregator_Aggregator($handle: int, $key: int, $limit: int, $val: int)
}
function {:inline} $Update'$1_aggregator_Aggregator'_handle(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(x, s->$key, s->$limit, s->$val)
}
function {:inline} $Update'$1_aggregator_Aggregator'_key(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(s->$handle, x, s->$limit, s->$val)
}
function {:inline} $Update'$1_aggregator_Aggregator'_limit(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(s->$handle, s->$key, x, s->$val)
}
function {:inline} $Update'$1_aggregator_Aggregator'_val(s: $1_aggregator_Aggregator, x: int): $1_aggregator_Aggregator {
    $1_aggregator_Aggregator(s->$handle, s->$key, s->$limit, x)
}
function $IsValid'$1_aggregator_Aggregator'(s: $1_aggregator_Aggregator): bool {
    $IsValid'address'(s->$handle)
      && $IsValid'address'(s->$key)
      && $IsValid'u128'(s->$limit)
      && $IsValid'u128'(s->$val)
}
function {:inline} $IsEqual'$1_aggregator_Aggregator'(s1: $1_aggregator_Aggregator, s2: $1_aggregator_Aggregator): bool {
    s1 == s2
}
function {:inline} $1_aggregator_spec_get_limit(s: $1_aggregator_Aggregator): int {
    s->$limit
}
function {:inline} $1_aggregator_spec_get_handle(s: $1_aggregator_Aggregator): int {
    s->$handle
}
function {:inline} $1_aggregator_spec_get_key(s: $1_aggregator_Aggregator): int {
    s->$key
}
function {:inline} $1_aggregator_spec_get_val(s: $1_aggregator_Aggregator): int {
    s->$val
}

function $1_aggregator_spec_read(agg: $1_aggregator_Aggregator): int {
    $1_aggregator_spec_get_val(agg)
}

function $1_aggregator_spec_aggregator_set_val(agg: $1_aggregator_Aggregator, val: int): $1_aggregator_Aggregator {
    $Update'$1_aggregator_Aggregator'_val(agg, val)
}

function $1_aggregator_spec_aggregator_get_val(agg: $1_aggregator_Aggregator): int {
    $1_aggregator_spec_get_val(agg)
}

function $1_aggregator_factory_spec_new_aggregator(limit: int) : $1_aggregator_Aggregator;

axiom (forall limit: int :: {$1_aggregator_factory_spec_new_aggregator(limit)}
    (var agg := $1_aggregator_factory_spec_new_aggregator(limit);
     $1_aggregator_spec_get_limit(agg) == limit));

axiom (forall limit: int :: {$1_aggregator_factory_spec_new_aggregator(limit)}
     (var agg := $1_aggregator_factory_spec_new_aggregator(limit);
     $1_aggregator_spec_aggregator_get_val(agg) == 0));


// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U16: int;
axiom $MAX_U16 == 65535;
const $MAX_U32: int;
axiom $MAX_U32 == 4294967295;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;
const $MAX_U256: int;
axiom $MAX_U256 == 115792089237316195423570985008687907853269984665640564039457584007913129639935;

// Templates for bitvector operations

function {:bvbuiltin "bvand"} $And'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvor"} $Or'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvxor"} $Xor'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvadd"} $Add'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvsub"} $Sub'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvmul"} $Mul'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvudiv"} $Div'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvurem"} $Mod'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvshl"} $Shl'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvlshr"} $Shr'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvult"} $Lt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv8'(bv8,bv8) returns(bool);

procedure {:inline 1} $AddBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Add'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $AddBv8_unchecked(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $SubBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv8'(src1, src2);
}

procedure {:inline 1} $MulBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Mul'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv8'(src1, src2);
}

procedure {:inline 1} $DivBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv8'(src1, src2);
}

procedure {:inline 1} $ModBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv8'(src1, src2);
}

procedure {:inline 1} $AndBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $And'Bv8'(src1,src2);
}

procedure {:inline 1} $OrBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Or'Bv8'(src1,src2);
}

procedure {:inline 1} $XorBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Xor'Bv8'(src1,src2);
}

procedure {:inline 1} $LtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Lt'Bv8'(src1,src2);
}

procedure {:inline 1} $LeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Le'Bv8'(src1,src2);
}

procedure {:inline 1} $GtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Gt'Bv8'(src1,src2);
}

procedure {:inline 1} $GeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Ge'Bv8'(src1,src2);
}

function $IsValid'bv8'(v: bv8): bool {
  $Ge'Bv8'(v,0bv8) && $Le'Bv8'(v,255bv8)
}

function {:inline} $IsEqual'bv8'(x: bv8, y: bv8): bool {
    x == y
}

procedure {:inline 1} $int2bv8(src: int) returns (dst: bv8)
{
    if (src > 255) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.8(src);
}

procedure {:inline 1} $bv2int8(src: bv8) returns (dst: int)
{
    dst := $bv2int.8(src);
}

function {:builtin "(_ int2bv 8)"} $int2bv.8(i: int) returns (bv8);
function {:builtin "bv2nat"} $bv2int.8(i: bv8) returns (int);

function {:bvbuiltin "bvand"} $And'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvor"} $Or'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvxor"} $Xor'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvadd"} $Add'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvsub"} $Sub'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvmul"} $Mul'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvudiv"} $Div'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvurem"} $Mod'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvshl"} $Shl'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvlshr"} $Shr'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvult"} $Lt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv16'(bv16,bv16) returns(bool);

procedure {:inline 1} $AddBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Add'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $AddBv16_unchecked(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $SubBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv16'(src1, src2);
}

procedure {:inline 1} $MulBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Mul'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv16'(src1, src2);
}

procedure {:inline 1} $DivBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv16'(src1, src2);
}

procedure {:inline 1} $ModBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv16'(src1, src2);
}

procedure {:inline 1} $AndBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $And'Bv16'(src1,src2);
}

procedure {:inline 1} $OrBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Or'Bv16'(src1,src2);
}

procedure {:inline 1} $XorBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Xor'Bv16'(src1,src2);
}

procedure {:inline 1} $LtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Lt'Bv16'(src1,src2);
}

procedure {:inline 1} $LeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Le'Bv16'(src1,src2);
}

procedure {:inline 1} $GtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Gt'Bv16'(src1,src2);
}

procedure {:inline 1} $GeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Ge'Bv16'(src1,src2);
}

function $IsValid'bv16'(v: bv16): bool {
  $Ge'Bv16'(v,0bv16) && $Le'Bv16'(v,65535bv16)
}

function {:inline} $IsEqual'bv16'(x: bv16, y: bv16): bool {
    x == y
}

procedure {:inline 1} $int2bv16(src: int) returns (dst: bv16)
{
    if (src > 65535) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.16(src);
}

procedure {:inline 1} $bv2int16(src: bv16) returns (dst: int)
{
    dst := $bv2int.16(src);
}

function {:builtin "(_ int2bv 16)"} $int2bv.16(i: int) returns (bv16);
function {:builtin "bv2nat"} $bv2int.16(i: bv16) returns (int);

function {:bvbuiltin "bvand"} $And'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvor"} $Or'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvxor"} $Xor'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvadd"} $Add'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsub"} $Sub'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvmul"} $Mul'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvudiv"} $Div'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvurem"} $Mod'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvshl"} $Shl'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} $Shr'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvult"} $Lt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv32'(bv32,bv32) returns(bool);

procedure {:inline 1} $AddBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Add'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $AddBv32_unchecked(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $SubBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv32'(src1, src2);
}

procedure {:inline 1} $MulBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Mul'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv32'(src1, src2);
}

procedure {:inline 1} $DivBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv32'(src1, src2);
}

procedure {:inline 1} $ModBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv32'(src1, src2);
}

procedure {:inline 1} $AndBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $And'Bv32'(src1,src2);
}

procedure {:inline 1} $OrBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Or'Bv32'(src1,src2);
}

procedure {:inline 1} $XorBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Xor'Bv32'(src1,src2);
}

procedure {:inline 1} $LtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Lt'Bv32'(src1,src2);
}

procedure {:inline 1} $LeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Le'Bv32'(src1,src2);
}

procedure {:inline 1} $GtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Gt'Bv32'(src1,src2);
}

procedure {:inline 1} $GeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Ge'Bv32'(src1,src2);
}

function $IsValid'bv32'(v: bv32): bool {
  $Ge'Bv32'(v,0bv32) && $Le'Bv32'(v,2147483647bv32)
}

function {:inline} $IsEqual'bv32'(x: bv32, y: bv32): bool {
    x == y
}

procedure {:inline 1} $int2bv32(src: int) returns (dst: bv32)
{
    if (src > 2147483647) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.32(src);
}

procedure {:inline 1} $bv2int32(src: bv32) returns (dst: int)
{
    dst := $bv2int.32(src);
}

function {:builtin "(_ int2bv 32)"} $int2bv.32(i: int) returns (bv32);
function {:builtin "bv2nat"} $bv2int.32(i: bv32) returns (int);

function {:bvbuiltin "bvand"} $And'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvor"} $Or'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvxor"} $Xor'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvadd"} $Add'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsub"} $Sub'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvmul"} $Mul'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvudiv"} $Div'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvurem"} $Mod'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvshl"} $Shl'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvlshr"} $Shr'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvult"} $Lt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv64'(bv64,bv64) returns(bool);

procedure {:inline 1} $AddBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Add'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $AddBv64_unchecked(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $SubBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv64'(src1, src2);
}

procedure {:inline 1} $MulBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Mul'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv64'(src1, src2);
}

procedure {:inline 1} $DivBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv64'(src1, src2);
}

procedure {:inline 1} $ModBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv64'(src1, src2);
}

procedure {:inline 1} $AndBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $And'Bv64'(src1,src2);
}

procedure {:inline 1} $OrBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Or'Bv64'(src1,src2);
}

procedure {:inline 1} $XorBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Xor'Bv64'(src1,src2);
}

procedure {:inline 1} $LtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Lt'Bv64'(src1,src2);
}

procedure {:inline 1} $LeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Le'Bv64'(src1,src2);
}

procedure {:inline 1} $GtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Gt'Bv64'(src1,src2);
}

procedure {:inline 1} $GeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Ge'Bv64'(src1,src2);
}

function $IsValid'bv64'(v: bv64): bool {
  $Ge'Bv64'(v,0bv64) && $Le'Bv64'(v,18446744073709551615bv64)
}

function {:inline} $IsEqual'bv64'(x: bv64, y: bv64): bool {
    x == y
}

procedure {:inline 1} $int2bv64(src: int) returns (dst: bv64)
{
    if (src > 18446744073709551615) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.64(src);
}

procedure {:inline 1} $bv2int64(src: bv64) returns (dst: int)
{
    dst := $bv2int.64(src);
}

function {:builtin "(_ int2bv 64)"} $int2bv.64(i: int) returns (bv64);
function {:builtin "bv2nat"} $bv2int.64(i: bv64) returns (int);

function {:bvbuiltin "bvand"} $And'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvor"} $Or'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvxor"} $Xor'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvadd"} $Add'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvsub"} $Sub'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvmul"} $Mul'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvudiv"} $Div'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvurem"} $Mod'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvshl"} $Shl'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvlshr"} $Shr'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvult"} $Lt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv128'(bv128,bv128) returns(bool);

procedure {:inline 1} $AddBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Add'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $AddBv128_unchecked(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $SubBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv128'(src1, src2);
}

procedure {:inline 1} $MulBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Mul'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv128'(src1, src2);
}

procedure {:inline 1} $DivBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv128'(src1, src2);
}

procedure {:inline 1} $ModBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv128'(src1, src2);
}

procedure {:inline 1} $AndBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $And'Bv128'(src1,src2);
}

procedure {:inline 1} $OrBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Or'Bv128'(src1,src2);
}

procedure {:inline 1} $XorBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Xor'Bv128'(src1,src2);
}

procedure {:inline 1} $LtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Lt'Bv128'(src1,src2);
}

procedure {:inline 1} $LeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Le'Bv128'(src1,src2);
}

procedure {:inline 1} $GtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Gt'Bv128'(src1,src2);
}

procedure {:inline 1} $GeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Ge'Bv128'(src1,src2);
}

function $IsValid'bv128'(v: bv128): bool {
  $Ge'Bv128'(v,0bv128) && $Le'Bv128'(v,340282366920938463463374607431768211455bv128)
}

function {:inline} $IsEqual'bv128'(x: bv128, y: bv128): bool {
    x == y
}

procedure {:inline 1} $int2bv128(src: int) returns (dst: bv128)
{
    if (src > 340282366920938463463374607431768211455) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.128(src);
}

procedure {:inline 1} $bv2int128(src: bv128) returns (dst: int)
{
    dst := $bv2int.128(src);
}

function {:builtin "(_ int2bv 128)"} $int2bv.128(i: int) returns (bv128);
function {:builtin "bv2nat"} $bv2int.128(i: bv128) returns (int);

function {:bvbuiltin "bvand"} $And'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvor"} $Or'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvxor"} $Xor'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvadd"} $Add'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvsub"} $Sub'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvmul"} $Mul'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvudiv"} $Div'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvurem"} $Mod'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvshl"} $Shl'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvlshr"} $Shr'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvult"} $Lt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv256'(bv256,bv256) returns(bool);

procedure {:inline 1} $AddBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Add'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $AddBv256_unchecked(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $SubBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv256'(src1, src2);
}

procedure {:inline 1} $MulBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Mul'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv256'(src1, src2);
}

procedure {:inline 1} $DivBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv256'(src1, src2);
}

procedure {:inline 1} $ModBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv256'(src1, src2);
}

procedure {:inline 1} $AndBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $And'Bv256'(src1,src2);
}

procedure {:inline 1} $OrBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Or'Bv256'(src1,src2);
}

procedure {:inline 1} $XorBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Xor'Bv256'(src1,src2);
}

procedure {:inline 1} $LtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Lt'Bv256'(src1,src2);
}

procedure {:inline 1} $LeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Le'Bv256'(src1,src2);
}

procedure {:inline 1} $GtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Gt'Bv256'(src1,src2);
}

procedure {:inline 1} $GeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Ge'Bv256'(src1,src2);
}

function $IsValid'bv256'(v: bv256): bool {
  $Ge'Bv256'(v,0bv256) && $Le'Bv256'(v,115792089237316195423570985008687907853269984665640564039457584007913129639935bv256)
}

function {:inline} $IsEqual'bv256'(x: bv256, y: bv256): bool {
    x == y
}

procedure {:inline 1} $int2bv256(src: int) returns (dst: bv256)
{
    if (src > 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.256(src);
}

procedure {:inline 1} $bv2int256(src: bv256) returns (dst: int)
{
    dst := $bv2int.256(src);
}

function {:builtin "(_ int2bv 256)"} $int2bv.256(i: int) returns (bv256);
function {:builtin "bv2nat"} $bv2int.256(i: bv256) returns (int);

datatype $Range {
    $Range(lb: int, ub: int)
}

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u16'(v: int): bool {
  v >= 0 && v <= $MAX_U16
}

function $IsValid'u32'(v: int): bool {
  v >= 0 && v <= $MAX_U32
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U64
}

function $IsValid'u128'(v: int): bool {
  v >= 0 && v <= $MAX_U128
}

function $IsValid'u256'(v: int): bool {
  v >= 0 && v <= $MAX_U256
}

function $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(r->lb) &&  $IsValid'u64'(r->ub)
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   r->lb <= i && i < r->ub
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u16'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u32'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u256'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

// ============================================================================================
// Memory

datatype $Location {
    // A global resource location within the statically known resource type's memory,
    // where `a` is an address.
    $Global(a: int),
    // A local location. `i` is the unique index of the local.
    $Local(i: int),
    // The location of a reference outside of the verification scope, for example, a `&mut` parameter
    // of the function being verified. References with these locations don't need to be written back
    // when mutation ends.
    $Param(i: int),
    // The location of an uninitialized mutation. Using this to make sure that the location
    // will not be equal to any valid mutation locations, i.e., $Local, $Global, or $Param.
    $Uninitialized()
}

// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
datatype $Mutation<T> {
    $Mutation(l: $Location, p: Vec int, v: T)
}

// Representation of memory for a given type.
datatype $Memory<T> {
    $Memory(domain: [int]bool, contents: [int]T)
}

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    ref->v
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(m->l, m->p, v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(m->l, ExtendVec(m->p, offset), v)
}

// Return true if two mutations share the location and path
function {:inline} $IsSameMutation<T1, T2>(parent: $Mutation T1, child: $Mutation T2 ): bool {
    parent->l == child->l && parent->p == child->p
}

// Return true if the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true if the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    m1->l == m2->l
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    (m->l) is $Global
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    m->l == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    (m->l)->a
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    m->domain[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    m->contents[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(m->domain[a := true], m->contents[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := false], m->contents)
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := s->domain[a]],
            m->contents[a := s->contents[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $Abort(code: int) {
    $abort_flag := true;
    $abort_code := code;
}

function {:inline} $StdError(cat: int, reason: int): int {
    reason * 256 + cat
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU16(src: int) returns (dst: int)
{
    if (src > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU32(src: int) returns (dst: int)
{
    if (src > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU256(src: int) returns (dst: int)
{
    if (src > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

// uninterpreted function to return an undefined value.
function $undefined_int(): int;

// Recursive exponentiation function
// Undefined unless e >=0.  $pow(0,0) is also undefined.
function $pow(n: int, e: int): int {
    if n != 0 && e == 0 then 1
    else if e > 0 then n * $pow(n, e - 1)
    else $undefined_int()
}

function $shl(src1: int, p: int): int {
    src1 * $pow(2, p)
}

function $shlU8(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 256
}

function $shlU16(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 65536
}

function $shlU32(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 4294967296
}

function $shlU64(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 18446744073709551616
}

function $shlU128(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 340282366920938463463374607431768211456
}

function $shlU256(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 115792089237316195423570985008687907853269984665640564039457584007913129639936
}

function $shr(src1: int, p: int): int {
    src1 div $pow(2, p)
}

// We need to know the size of the destination in order to drop bits
// that have been shifted left more than that, so we have $ShlU8/16/32/64/128/256
procedure {:inline 1} $ShlU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU8(src1, src2);
}

// Template for cast and shift operations of bitvector types

procedure {:inline 1} $CastBv8to8(src: bv8) returns (dst: bv8)
{
    dst := src;
}


function $shlBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shl'Bv8'(src1, src2)
}

procedure {:inline 1} $ShlBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2);
}

function $shrBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shr'Bv8'(src1, src2)
}

procedure {:inline 1} $ShrBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2);
}

procedure {:inline 1} $CastBv16to8(src: bv16) returns (dst: bv8)
{
    if ($Gt'Bv16'(src, 255bv16)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv32to8(src: bv32) returns (dst: bv8)
{
    if ($Gt'Bv32'(src, 255bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv64to8(src: bv64) returns (dst: bv8)
{
    if ($Gt'Bv64'(src, 255bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv128to8(src: bv128) returns (dst: bv8)
{
    if ($Gt'Bv128'(src, 255bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv256to8(src: bv256) returns (dst: bv8)
{
    if ($Gt'Bv256'(src, 255bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv8to16(src: bv8) returns (dst: bv16)
{
    dst := 0bv8 ++ src;
}


function $shlBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shl'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShlBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, 0bv8 ++ src2);
}

function $shrBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shr'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShrBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, 0bv8 ++ src2);
}

procedure {:inline 1} $CastBv16to16(src: bv16) returns (dst: bv16)
{
    dst := src;
}


function $shlBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shl'Bv16'(src1, src2)
}

procedure {:inline 1} $ShlBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2);
}

function $shrBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shr'Bv16'(src1, src2)
}

procedure {:inline 1} $ShrBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2);
}

procedure {:inline 1} $CastBv32to16(src: bv32) returns (dst: bv16)
{
    if ($Gt'Bv32'(src, 65535bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv64to16(src: bv64) returns (dst: bv16)
{
    if ($Gt'Bv64'(src, 65535bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv128to16(src: bv128) returns (dst: bv16)
{
    if ($Gt'Bv128'(src, 65535bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv256to16(src: bv256) returns (dst: bv16)
{
    if ($Gt'Bv256'(src, 65535bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv8to32(src: bv8) returns (dst: bv32)
{
    dst := 0bv24 ++ src;
}


function $shlBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShlBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv24 ++ src2);
}

function $shrBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShrBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv24 ++ src2);
}

procedure {:inline 1} $CastBv16to32(src: bv16) returns (dst: bv32)
{
    dst := 0bv16 ++ src;
}


function $shlBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShlBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv16 ++ src2);
}

function $shrBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShrBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv16 ++ src2);
}

procedure {:inline 1} $CastBv32to32(src: bv32) returns (dst: bv32)
{
    dst := src;
}


function $shlBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shl'Bv32'(src1, src2)
}

procedure {:inline 1} $ShlBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2);
}

function $shrBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shr'Bv32'(src1, src2)
}

procedure {:inline 1} $ShrBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2);
}

procedure {:inline 1} $CastBv64to32(src: bv64) returns (dst: bv32)
{
    if ($Gt'Bv64'(src, 2147483647bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv128to32(src: bv128) returns (dst: bv32)
{
    if ($Gt'Bv128'(src, 2147483647bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv256to32(src: bv256) returns (dst: bv32)
{
    if ($Gt'Bv256'(src, 2147483647bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv8to64(src: bv8) returns (dst: bv64)
{
    dst := 0bv56 ++ src;
}


function $shlBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShlBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv56 ++ src2);
}

function $shrBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShrBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv56 ++ src2);
}

procedure {:inline 1} $CastBv16to64(src: bv16) returns (dst: bv64)
{
    dst := 0bv48 ++ src;
}


function $shlBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShlBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv48 ++ src2);
}

function $shrBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShrBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv48 ++ src2);
}

procedure {:inline 1} $CastBv32to64(src: bv32) returns (dst: bv64)
{
    dst := 0bv32 ++ src;
}


function $shlBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShlBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv32 ++ src2);
}

function $shrBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShrBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv32 ++ src2);
}

procedure {:inline 1} $CastBv64to64(src: bv64) returns (dst: bv64)
{
    dst := src;
}


function $shlBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shl'Bv64'(src1, src2)
}

procedure {:inline 1} $ShlBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2);
}

function $shrBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shr'Bv64'(src1, src2)
}

procedure {:inline 1} $ShrBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2);
}

procedure {:inline 1} $CastBv128to64(src: bv128) returns (dst: bv64)
{
    if ($Gt'Bv128'(src, 18446744073709551615bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv256to64(src: bv256) returns (dst: bv64)
{
    if ($Gt'Bv256'(src, 18446744073709551615bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv8to128(src: bv8) returns (dst: bv128)
{
    dst := 0bv120 ++ src;
}


function $shlBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShlBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv120 ++ src2);
}

function $shrBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShrBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv120 ++ src2);
}

procedure {:inline 1} $CastBv16to128(src: bv16) returns (dst: bv128)
{
    dst := 0bv112 ++ src;
}


function $shlBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShlBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv112 ++ src2);
}

function $shrBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShrBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv112 ++ src2);
}

procedure {:inline 1} $CastBv32to128(src: bv32) returns (dst: bv128)
{
    dst := 0bv96 ++ src;
}


function $shlBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShlBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv96 ++ src2);
}

function $shrBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShrBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv96 ++ src2);
}

procedure {:inline 1} $CastBv64to128(src: bv64) returns (dst: bv128)
{
    dst := 0bv64 ++ src;
}


function $shlBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShlBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv64 ++ src2);
}

function $shrBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShrBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv64 ++ src2);
}

procedure {:inline 1} $CastBv128to128(src: bv128) returns (dst: bv128)
{
    dst := src;
}


function $shlBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shl'Bv128'(src1, src2)
}

procedure {:inline 1} $ShlBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2);
}

function $shrBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shr'Bv128'(src1, src2)
}

procedure {:inline 1} $ShrBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2);
}

procedure {:inline 1} $CastBv256to128(src: bv256) returns (dst: bv128)
{
    if ($Gt'Bv256'(src, 340282366920938463463374607431768211455bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[128:0];
}


function $shlBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shl'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShlBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2[128:0]);
}

function $shrBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shr'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShrBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2[128:0]);
}

procedure {:inline 1} $CastBv8to256(src: bv8) returns (dst: bv256)
{
    dst := 0bv248 ++ src;
}


function $shlBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShlBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv248 ++ src2);
}

function $shrBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShrBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv248 ++ src2);
}

procedure {:inline 1} $CastBv16to256(src: bv16) returns (dst: bv256)
{
    dst := 0bv240 ++ src;
}


function $shlBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShlBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv240 ++ src2);
}

function $shrBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShrBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv240 ++ src2);
}

procedure {:inline 1} $CastBv32to256(src: bv32) returns (dst: bv256)
{
    dst := 0bv224 ++ src;
}


function $shlBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShlBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv224 ++ src2);
}

function $shrBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShrBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv224 ++ src2);
}

procedure {:inline 1} $CastBv64to256(src: bv64) returns (dst: bv256)
{
    dst := 0bv192 ++ src;
}


function $shlBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShlBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv192 ++ src2);
}

function $shrBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShrBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv192 ++ src2);
}

procedure {:inline 1} $CastBv128to256(src: bv128) returns (dst: bv256)
{
    dst := 0bv128 ++ src;
}


function $shlBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShlBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv128 ++ src2);
}

function $shrBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShrBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv128 ++ src2);
}

procedure {:inline 1} $CastBv256to256(src: bv256) returns (dst: bv256)
{
    dst := src;
}


function $shlBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shl'Bv256'(src1, src2)
}

procedure {:inline 1} $ShlBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, src2);
}

function $shrBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shr'Bv256'(src1, src2)
}

procedure {:inline 1} $ShrBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, src2);
}

procedure {:inline 1} $ShlU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU16(src1, src2);
}

procedure {:inline 1} $ShlU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU32(src1, src2);
}

procedure {:inline 1} $ShlU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
       call $ExecFailureAbort();
       return;
    }
    dst := $shlU64(src1, src2);
}

procedure {:inline 1} $ShlU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU128(src1, src2);
}

procedure {:inline 1} $ShlU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shlU256(src1, src2);
}

procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, r->lb, r->ub)
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$42_simple10_Person`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$42_simple10_Person''(v1: Vec ($42_simple10_Person), v2: Vec ($42_simple10_Person)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$42_simple10_Person'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$42_simple10_Person''(v: Vec ($42_simple10_Person), prefix: Vec ($42_simple10_Person)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$42_simple10_Person'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$42_simple10_Person''(v: Vec ($42_simple10_Person), suffix: Vec ($42_simple10_Person)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$42_simple10_Person'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$42_simple10_Person''(v: Vec ($42_simple10_Person)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$42_simple10_Person'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$42_simple10_Person'(v: Vec ($42_simple10_Person), e: $42_simple10_Person): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$42_simple10_Person'(ReadVec(v, i), e))
}

function $IndexOfVec'$42_simple10_Person'(v: Vec ($42_simple10_Person), e: $42_simple10_Person): int;
axiom (forall v: Vec ($42_simple10_Person), e: $42_simple10_Person:: {$IndexOfVec'$42_simple10_Person'(v, e)}
    (var i := $IndexOfVec'$42_simple10_Person'(v, e);
     if (!$ContainsVec'$42_simple10_Person'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$42_simple10_Person'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$42_simple10_Person'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$42_simple10_Person'(v: Vec ($42_simple10_Person)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$42_simple10_Person'(): Vec ($42_simple10_Person) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$42_simple10_Person'() returns (v: Vec ($42_simple10_Person)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$42_simple10_Person'(): Vec ($42_simple10_Person) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$42_simple10_Person'(v: Vec ($42_simple10_Person)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person)), val: $42_simple10_Person) returns (m': $Mutation (Vec ($42_simple10_Person))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$42_simple10_Person'(v: Vec ($42_simple10_Person), val: $42_simple10_Person): Vec ($42_simple10_Person) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person))) returns (e: $42_simple10_Person, m': $Mutation (Vec ($42_simple10_Person))) {
    var v: Vec ($42_simple10_Person);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person)), other: Vec ($42_simple10_Person)) returns (m': $Mutation (Vec ($42_simple10_Person))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person))) returns (m': $Mutation (Vec ($42_simple10_Person))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person)), other: Vec ($42_simple10_Person)) returns (m': $Mutation (Vec ($42_simple10_Person))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person)), new_len: int) returns (v: (Vec ($42_simple10_Person)), m': $Mutation (Vec ($42_simple10_Person))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person)), new_len: int) returns (v: (Vec ($42_simple10_Person)), m': $Mutation (Vec ($42_simple10_Person))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person)), left: int, right: int) returns (m': $Mutation (Vec ($42_simple10_Person))) {
    var left_vec: Vec ($42_simple10_Person);
    var mid_vec: Vec ($42_simple10_Person);
    var right_vec: Vec ($42_simple10_Person);
    var v: Vec ($42_simple10_Person);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person)), rot: int) returns (n: int, m': $Mutation (Vec ($42_simple10_Person))) {
    var v: Vec ($42_simple10_Person);
    var len: int;
    var left_vec: Vec ($42_simple10_Person);
    var right_vec: Vec ($42_simple10_Person);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($42_simple10_Person))) {
    var left_vec: Vec ($42_simple10_Person);
    var mid_vec: Vec ($42_simple10_Person);
    var right_vec: Vec ($42_simple10_Person);
    var mid_left_vec: Vec ($42_simple10_Person);
    var mid_right_vec: Vec ($42_simple10_Person);
    var v: Vec ($42_simple10_Person);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person)), i: int, e: $42_simple10_Person) returns (m': $Mutation (Vec ($42_simple10_Person))) {
    var left_vec: Vec ($42_simple10_Person);
    var right_vec: Vec ($42_simple10_Person);
    var v: Vec ($42_simple10_Person);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'$42_simple10_Person'(v: Vec ($42_simple10_Person)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$42_simple10_Person'(v: Vec ($42_simple10_Person)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$42_simple10_Person'(v: Vec ($42_simple10_Person), i: int) returns (dst: $42_simple10_Person) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$42_simple10_Person'(v: Vec ($42_simple10_Person), i: int): $42_simple10_Person {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person)), index: int)
returns (dst: $Mutation ($42_simple10_Person), m': $Mutation (Vec ($42_simple10_Person)))
{
    var v: Vec ($42_simple10_Person);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$42_simple10_Person'(v: Vec ($42_simple10_Person), i: int): $42_simple10_Person {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$42_simple10_Person'(v: Vec ($42_simple10_Person)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person)), i: int, j: int) returns (m': $Mutation (Vec ($42_simple10_Person)))
{
    var v: Vec ($42_simple10_Person);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$42_simple10_Person'(v: Vec ($42_simple10_Person), i: int, j: int): Vec ($42_simple10_Person) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person)), i: int) returns (e: $42_simple10_Person, m': $Mutation (Vec ($42_simple10_Person)))
{
    var v: Vec ($42_simple10_Person);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$42_simple10_Person'(m: $Mutation (Vec ($42_simple10_Person)), i: int) returns (e: $42_simple10_Person, m': $Mutation (Vec ($42_simple10_Person)))
{
    var len: int;
    var v: Vec ($42_simple10_Person);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$42_simple10_Person'(v: Vec ($42_simple10_Person), e: $42_simple10_Person) returns (res: bool)  {
    res := $ContainsVec'$42_simple10_Person'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$42_simple10_Person'(v: Vec ($42_simple10_Person), e: $42_simple10_Person) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$42_simple10_Person'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$42_simple11_Employee`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$42_simple11_Employee''(v1: Vec ($42_simple11_Employee), v2: Vec ($42_simple11_Employee)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$42_simple11_Employee'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$42_simple11_Employee''(v: Vec ($42_simple11_Employee), prefix: Vec ($42_simple11_Employee)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$42_simple11_Employee'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$42_simple11_Employee''(v: Vec ($42_simple11_Employee), suffix: Vec ($42_simple11_Employee)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$42_simple11_Employee'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$42_simple11_Employee''(v: Vec ($42_simple11_Employee)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$42_simple11_Employee'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$42_simple11_Employee'(v: Vec ($42_simple11_Employee), e: $42_simple11_Employee): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$42_simple11_Employee'(ReadVec(v, i), e))
}

function $IndexOfVec'$42_simple11_Employee'(v: Vec ($42_simple11_Employee), e: $42_simple11_Employee): int;
axiom (forall v: Vec ($42_simple11_Employee), e: $42_simple11_Employee:: {$IndexOfVec'$42_simple11_Employee'(v, e)}
    (var i := $IndexOfVec'$42_simple11_Employee'(v, e);
     if (!$ContainsVec'$42_simple11_Employee'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$42_simple11_Employee'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$42_simple11_Employee'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$42_simple11_Employee'(v: Vec ($42_simple11_Employee)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$42_simple11_Employee'(): Vec ($42_simple11_Employee) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$42_simple11_Employee'() returns (v: Vec ($42_simple11_Employee)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$42_simple11_Employee'(): Vec ($42_simple11_Employee) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$42_simple11_Employee'(v: Vec ($42_simple11_Employee)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee)), val: $42_simple11_Employee) returns (m': $Mutation (Vec ($42_simple11_Employee))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$42_simple11_Employee'(v: Vec ($42_simple11_Employee), val: $42_simple11_Employee): Vec ($42_simple11_Employee) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee))) returns (e: $42_simple11_Employee, m': $Mutation (Vec ($42_simple11_Employee))) {
    var v: Vec ($42_simple11_Employee);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee)), other: Vec ($42_simple11_Employee)) returns (m': $Mutation (Vec ($42_simple11_Employee))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee))) returns (m': $Mutation (Vec ($42_simple11_Employee))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee)), other: Vec ($42_simple11_Employee)) returns (m': $Mutation (Vec ($42_simple11_Employee))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee)), new_len: int) returns (v: (Vec ($42_simple11_Employee)), m': $Mutation (Vec ($42_simple11_Employee))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee)), new_len: int) returns (v: (Vec ($42_simple11_Employee)), m': $Mutation (Vec ($42_simple11_Employee))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee)), left: int, right: int) returns (m': $Mutation (Vec ($42_simple11_Employee))) {
    var left_vec: Vec ($42_simple11_Employee);
    var mid_vec: Vec ($42_simple11_Employee);
    var right_vec: Vec ($42_simple11_Employee);
    var v: Vec ($42_simple11_Employee);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee)), rot: int) returns (n: int, m': $Mutation (Vec ($42_simple11_Employee))) {
    var v: Vec ($42_simple11_Employee);
    var len: int;
    var left_vec: Vec ($42_simple11_Employee);
    var right_vec: Vec ($42_simple11_Employee);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($42_simple11_Employee))) {
    var left_vec: Vec ($42_simple11_Employee);
    var mid_vec: Vec ($42_simple11_Employee);
    var right_vec: Vec ($42_simple11_Employee);
    var mid_left_vec: Vec ($42_simple11_Employee);
    var mid_right_vec: Vec ($42_simple11_Employee);
    var v: Vec ($42_simple11_Employee);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee)), i: int, e: $42_simple11_Employee) returns (m': $Mutation (Vec ($42_simple11_Employee))) {
    var left_vec: Vec ($42_simple11_Employee);
    var right_vec: Vec ($42_simple11_Employee);
    var v: Vec ($42_simple11_Employee);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'$42_simple11_Employee'(v: Vec ($42_simple11_Employee)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$42_simple11_Employee'(v: Vec ($42_simple11_Employee)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$42_simple11_Employee'(v: Vec ($42_simple11_Employee), i: int) returns (dst: $42_simple11_Employee) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$42_simple11_Employee'(v: Vec ($42_simple11_Employee), i: int): $42_simple11_Employee {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee)), index: int)
returns (dst: $Mutation ($42_simple11_Employee), m': $Mutation (Vec ($42_simple11_Employee)))
{
    var v: Vec ($42_simple11_Employee);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$42_simple11_Employee'(v: Vec ($42_simple11_Employee), i: int): $42_simple11_Employee {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$42_simple11_Employee'(v: Vec ($42_simple11_Employee)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee)), i: int, j: int) returns (m': $Mutation (Vec ($42_simple11_Employee)))
{
    var v: Vec ($42_simple11_Employee);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$42_simple11_Employee'(v: Vec ($42_simple11_Employee), i: int, j: int): Vec ($42_simple11_Employee) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee)), i: int) returns (e: $42_simple11_Employee, m': $Mutation (Vec ($42_simple11_Employee)))
{
    var v: Vec ($42_simple11_Employee);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$42_simple11_Employee'(m: $Mutation (Vec ($42_simple11_Employee)), i: int) returns (e: $42_simple11_Employee, m': $Mutation (Vec ($42_simple11_Employee)))
{
    var len: int;
    var v: Vec ($42_simple11_Employee);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$42_simple11_Employee'(v: Vec ($42_simple11_Employee), e: $42_simple11_Employee) returns (res: bool)  {
    res := $ContainsVec'$42_simple11_Employee'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$42_simple11_Employee'(v: Vec ($42_simple11_Employee), e: $42_simple11_Employee) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$42_simple11_Employee'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$42_simple12_Employee`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$42_simple12_Employee''(v1: Vec ($42_simple12_Employee), v2: Vec ($42_simple12_Employee)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$42_simple12_Employee'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'$42_simple12_Employee''(v: Vec ($42_simple12_Employee), prefix: Vec ($42_simple12_Employee)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'$42_simple12_Employee'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'$42_simple12_Employee''(v: Vec ($42_simple12_Employee), suffix: Vec ($42_simple12_Employee)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'$42_simple12_Employee'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'$42_simple12_Employee''(v: Vec ($42_simple12_Employee)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$42_simple12_Employee'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$42_simple12_Employee'(v: Vec ($42_simple12_Employee), e: $42_simple12_Employee): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$42_simple12_Employee'(ReadVec(v, i), e))
}

function $IndexOfVec'$42_simple12_Employee'(v: Vec ($42_simple12_Employee), e: $42_simple12_Employee): int;
axiom (forall v: Vec ($42_simple12_Employee), e: $42_simple12_Employee:: {$IndexOfVec'$42_simple12_Employee'(v, e)}
    (var i := $IndexOfVec'$42_simple12_Employee'(v, e);
     if (!$ContainsVec'$42_simple12_Employee'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$42_simple12_Employee'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$42_simple12_Employee'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$42_simple12_Employee'(v: Vec ($42_simple12_Employee)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$42_simple12_Employee'(): Vec ($42_simple12_Employee) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$42_simple12_Employee'() returns (v: Vec ($42_simple12_Employee)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$42_simple12_Employee'(): Vec ($42_simple12_Employee) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$42_simple12_Employee'(v: Vec ($42_simple12_Employee)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee)), val: $42_simple12_Employee) returns (m': $Mutation (Vec ($42_simple12_Employee))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$42_simple12_Employee'(v: Vec ($42_simple12_Employee), val: $42_simple12_Employee): Vec ($42_simple12_Employee) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee))) returns (e: $42_simple12_Employee, m': $Mutation (Vec ($42_simple12_Employee))) {
    var v: Vec ($42_simple12_Employee);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee)), other: Vec ($42_simple12_Employee)) returns (m': $Mutation (Vec ($42_simple12_Employee))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee))) returns (m': $Mutation (Vec ($42_simple12_Employee))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee)), other: Vec ($42_simple12_Employee)) returns (m': $Mutation (Vec ($42_simple12_Employee))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee)), new_len: int) returns (v: (Vec ($42_simple12_Employee)), m': $Mutation (Vec ($42_simple12_Employee))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee)), new_len: int) returns (v: (Vec ($42_simple12_Employee)), m': $Mutation (Vec ($42_simple12_Employee))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee)), left: int, right: int) returns (m': $Mutation (Vec ($42_simple12_Employee))) {
    var left_vec: Vec ($42_simple12_Employee);
    var mid_vec: Vec ($42_simple12_Employee);
    var right_vec: Vec ($42_simple12_Employee);
    var v: Vec ($42_simple12_Employee);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee)), rot: int) returns (n: int, m': $Mutation (Vec ($42_simple12_Employee))) {
    var v: Vec ($42_simple12_Employee);
    var len: int;
    var left_vec: Vec ($42_simple12_Employee);
    var right_vec: Vec ($42_simple12_Employee);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ($42_simple12_Employee))) {
    var left_vec: Vec ($42_simple12_Employee);
    var mid_vec: Vec ($42_simple12_Employee);
    var right_vec: Vec ($42_simple12_Employee);
    var mid_left_vec: Vec ($42_simple12_Employee);
    var mid_right_vec: Vec ($42_simple12_Employee);
    var v: Vec ($42_simple12_Employee);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee)), i: int, e: $42_simple12_Employee) returns (m': $Mutation (Vec ($42_simple12_Employee))) {
    var left_vec: Vec ($42_simple12_Employee);
    var right_vec: Vec ($42_simple12_Employee);
    var v: Vec ($42_simple12_Employee);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'$42_simple12_Employee'(v: Vec ($42_simple12_Employee)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$42_simple12_Employee'(v: Vec ($42_simple12_Employee)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$42_simple12_Employee'(v: Vec ($42_simple12_Employee), i: int) returns (dst: $42_simple12_Employee) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$42_simple12_Employee'(v: Vec ($42_simple12_Employee), i: int): $42_simple12_Employee {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee)), index: int)
returns (dst: $Mutation ($42_simple12_Employee), m': $Mutation (Vec ($42_simple12_Employee)))
{
    var v: Vec ($42_simple12_Employee);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$42_simple12_Employee'(v: Vec ($42_simple12_Employee), i: int): $42_simple12_Employee {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$42_simple12_Employee'(v: Vec ($42_simple12_Employee)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee)), i: int, j: int) returns (m': $Mutation (Vec ($42_simple12_Employee)))
{
    var v: Vec ($42_simple12_Employee);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$42_simple12_Employee'(v: Vec ($42_simple12_Employee), i: int, j: int): Vec ($42_simple12_Employee) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee)), i: int) returns (e: $42_simple12_Employee, m': $Mutation (Vec ($42_simple12_Employee)))
{
    var v: Vec ($42_simple12_Employee);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$42_simple12_Employee'(m: $Mutation (Vec ($42_simple12_Employee)), i: int) returns (e: $42_simple12_Employee, m': $Mutation (Vec ($42_simple12_Employee)))
{
    var len: int;
    var v: Vec ($42_simple12_Employee);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$42_simple12_Employee'(v: Vec ($42_simple12_Employee), e: $42_simple12_Employee) returns (res: bool)  {
    res := $ContainsVec'$42_simple12_Employee'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$42_simple12_Employee'(v: Vec ($42_simple12_Employee), e: $42_simple12_Employee) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$42_simple12_Employee'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u8''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u8''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'u8'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'u8'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'u8'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var mid_left_vec: Vec (int);
    var mid_right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'u8'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `bv8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'bv8''(v1: Vec (bv8), v2: Vec (bv8)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'bv8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'bv8''(v: Vec (bv8), prefix: Vec (bv8)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'bv8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'bv8''(v: Vec (bv8), suffix: Vec (bv8)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'bv8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'bv8''(v: Vec (bv8)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'bv8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'bv8'(v: Vec (bv8), e: bv8): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv8'(ReadVec(v, i), e))
}

function $IndexOfVec'bv8'(v: Vec (bv8), e: bv8): int;
axiom (forall v: Vec (bv8), e: bv8:: {$IndexOfVec'bv8'(v, e)}
    (var i := $IndexOfVec'bv8'(v, e);
     if (!$ContainsVec'bv8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'bv8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'bv8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'bv8'(v: Vec (bv8)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'bv8'(): Vec (bv8) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'bv8'() returns (v: Vec (bv8)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'bv8'(): Vec (bv8) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'bv8'(v: Vec (bv8)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'bv8'(m: $Mutation (Vec (bv8)), val: bv8) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'bv8'(v: Vec (bv8), val: bv8): Vec (bv8) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'bv8'(m: $Mutation (Vec (bv8))) returns (e: bv8, m': $Mutation (Vec (bv8))) {
    var v: Vec (bv8);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'bv8'(m: $Mutation (Vec (bv8)), other: Vec (bv8)) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'bv8'(m: $Mutation (Vec (bv8))) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'bv8'(m: $Mutation (Vec (bv8)), other: Vec (bv8)) returns (m': $Mutation (Vec (bv8))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'bv8'(m: $Mutation (Vec (bv8)), new_len: int) returns (v: (Vec (bv8)), m': $Mutation (Vec (bv8))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'bv8'(m: $Mutation (Vec (bv8)), new_len: int) returns (v: (Vec (bv8)), m': $Mutation (Vec (bv8))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'bv8'(m: $Mutation (Vec (bv8)), left: int, right: int) returns (m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var mid_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var v: Vec (bv8);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'bv8'(m: $Mutation (Vec (bv8)), rot: int) returns (n: int, m': $Mutation (Vec (bv8))) {
    var v: Vec (bv8);
    var len: int;
    var left_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'bv8'(m: $Mutation (Vec (bv8)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var mid_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var mid_left_vec: Vec (bv8);
    var mid_right_vec: Vec (bv8);
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'bv8'(m: $Mutation (Vec (bv8)), i: int, e: bv8) returns (m': $Mutation (Vec (bv8))) {
    var left_vec: Vec (bv8);
    var right_vec: Vec (bv8);
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'bv8'(v: Vec (bv8)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'bv8'(v: Vec (bv8)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'bv8'(v: Vec (bv8), i: int) returns (dst: bv8) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'bv8'(v: Vec (bv8), i: int): bv8 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'bv8'(m: $Mutation (Vec (bv8)), index: int)
returns (dst: $Mutation (bv8), m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'bv8'(v: Vec (bv8), i: int): bv8 {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'bv8'(v: Vec (bv8)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'bv8'(m: $Mutation (Vec (bv8)), i: int, j: int) returns (m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'bv8'(v: Vec (bv8), i: int, j: int): Vec (bv8) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'bv8'(m: $Mutation (Vec (bv8)), i: int) returns (e: bv8, m': $Mutation (Vec (bv8)))
{
    var v: Vec (bv8);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'bv8'(m: $Mutation (Vec (bv8)), i: int) returns (e: bv8, m': $Mutation (Vec (bv8)))
{
    var len: int;
    var v: Vec (bv8);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'bv8'(v: Vec (bv8), e: bv8) returns (res: bool)  {
    res := $ContainsVec'bv8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'bv8'(v: Vec (bv8), e: bv8) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'bv8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ==================================================================================
// Native Table

// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_hash_sha2(v1), $1_hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha2(v1), $1_hash_sha2(v2)));

procedure $1_hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha2_256(val: Vec int): Vec int {
    $1_hash_sha2(val)
}

// similarly for Hash_sha3
function $1_hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_hash_sha3(v1), $1_hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha3(v1), $1_hash_sha3(v2)));

procedure $1_hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha3_256(val: Vec int): Vec int {
    $1_hash_sha3(val)
}

// ==================================================================================
// Native string

// TODO: correct implementation of strings

procedure {:inline 1} $1_string_internal_check_utf8(x: Vec int) returns (r: bool) {
}

procedure {:inline 1} $1_string_internal_sub_string(x: Vec int, i: int, j: int) returns (r: Vec int) {
}

procedure {:inline 1} $1_string_internal_index_of(x: Vec int, y: Vec int) returns (r: int) {
}

procedure {:inline 1} $1_string_internal_is_char_boundary(x: Vec int, i: int) returns (r: bool) {
}




// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native account

procedure {:inline 1} $1_Account_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

// ==================================================================================
// Native Signer

datatype $signer {
    $signer($addr: int)
}
function {:inline} $IsValid'signer'(s: $signer): bool {
    $IsValid'address'(s->$addr)
}
function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    s1 == s2
}

procedure {:inline 1} $1_signer_borrow_address(signer: $signer) returns (res: int) {
    res := signer->$addr;
}

function {:inline} $1_signer_$borrow_address(signer: $signer): int
{
    signer->$addr
}

function $1_signer_is_txn_signer(s: $signer): bool;

function $1_signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native bcs::serialize


// ==================================================================================
// Native Event module



procedure {:inline 1} $InitEventStore() {
}

// ============================================================================================
// Type Reflection on Type Parameters

datatype $TypeParamInfo {
    $TypeParamBool(),
    $TypeParamU8(),
    $TypeParamU16(),
    $TypeParamU32(),
    $TypeParamU64(),
    $TypeParamU128(),
    $TypeParamU256(),
    $TypeParamAddress(),
    $TypeParamSigner(),
    $TypeParamVector(e: $TypeParamInfo),
    $TypeParamStruct(a: int, m: Vec int, s: Vec int)
}



//==================================
// Begin Translation

function $TypeName(t: $TypeParamInfo): Vec int;
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamBool ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)) ==> t is $TypeParamBool);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU8 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)) ==> t is $TypeParamU8);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU16 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)) ==> t is $TypeParamU16);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU32 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)) ==> t is $TypeParamU32);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU64 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)) ==> t is $TypeParamU64);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU128 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)) ==> t is $TypeParamU128);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU256 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)) ==> t is $TypeParamU256);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamAddress ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)) ==> t is $TypeParamAddress);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamSigner ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)) ==> t is $TypeParamSigner);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamVector ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7), $TypeName(t->e)), Vec(DefaultVecMap()[0 := 62], 1))));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} ($IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7)) && $IsSuffix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 62], 1))) ==> t is $TypeParamVector);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamStruct ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 48][1 := 120], 2), MakeVec1(t->a)), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), t->m), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), t->s)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 48][1 := 120], 2)) ==> t is $TypeParamVector);


// Given Types for Type Parameters

type #0;
function {:inline} $IsEqual'#0'(x1: #0, x2: #0): bool { x1 == x2 }
function {:inline} $IsValid'#0'(x: #0): bool { true }
var #0_info: $TypeParamInfo;
var #0_$memory: $Memory #0;

// fun MathModule::identity [verification] at /mnt/c/Users/DELL/move-tut/sources/simple15.move:4:5+51
procedure {:timeLimit 40} $42_MathModule_identity$verify(_$t0: #0) returns ($ret0: #0)
{
    // declare local variables
    var $t0: #0;
    var $temp_0'#0': #0;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple15.move:4:5+1
    assume {:print "$at(9,133,134)"} true;
    assume $IsValid'#0'($t0);

    // trace_local[x]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple15.move:4:5+1
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple15.move:5:9+1
    assume {:print "$at(9,176,177)"} true;
    assume {:print "$track_return(1,0,0):", $t0} $t0 == $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple15.move:6:5+1
    assume {:print "$at(9,183,184)"} true;
L1:

    // return $t0 at /mnt/c/Users/DELL/move-tut/sources/simple15.move:6:5+1
    assume {:print "$at(9,183,184)"} true;
    $ret0 := $t0;
    return;

}

// spec fun at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.spec.move:28:9+50
function  $1_string_spec_internal_check_utf8(v: Vec (int)): bool;
axiom (forall v: Vec (int) ::
(var $$res := $1_string_spec_internal_check_utf8(v);
$IsValid'bool'($$res)));

// struct string::String at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:13:5+70
datatype $1_string_String {
    $1_string_String($bytes: Vec (int))
}
function {:inline} $Update'$1_string_String'_bytes(s: $1_string_String, x: Vec (int)): $1_string_String {
    $1_string_String(x)
}
function $IsValid'$1_string_String'(s: $1_string_String): bool {
    $IsValid'vec'u8''(s->$bytes)
}
function {:inline} $IsEqual'$1_string_String'(s1: $1_string_String, s2: $1_string_String): bool {
    $IsEqual'vec'u8''(s1->$bytes, s2->$bytes)}

// fun string::utf8 [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:18:5+133
procedure {:inline 1} $1_string_utf8(_$t0: Vec (int)) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t3: $1_string_String;
    var $t0: Vec (int);
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[bytes]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:18:5+1
    assume {:print "$at(28,573,574)"} true;
    assume {:print "$track_local(3,13,0):", $t0} $t0 == $t0;

    // $t1 := opaque begin: string::internal_check_utf8($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:17+27
    assume {:print "$at(28,634,661)"} true;

    // assume WellFormed($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:17+27
    assume $IsValid'bool'($t1);

    // assume Eq<bool>($t1, string::spec_internal_check_utf8($t0)) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:17+27
    assume $IsEqual'bool'($t1, $1_string_spec_internal_check_utf8($t0));

    // $t1 := opaque end: string::internal_check_utf8($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:17+27

    // if ($t1) goto L1 else goto L0 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:9+51
    if ($t1) { goto L1; } else { goto L0; }

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:9+51
L1:

    // goto L2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:9+51
    assume {:print "$at(28,626,677)"} true;
    goto L2;

    // label L0 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:46+13
L0:

    // $t2 := 1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:46+13
    assume {:print "$at(28,663,676)"} true;
    $t2 := 1;
    assume $IsValid'u64'($t2);

    // trace_abort($t2) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:9+51
    assume {:print "$at(28,626,677)"} true;
    assume {:print "$track_abort(3,13):", $t2} $t2 == $t2;

    // goto L4 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:19:9+51
    goto L4;

    // label L2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:20:16+5
    assume {:print "$at(28,694,699)"} true;
L2:

    // $t3 := pack string::String($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:20:9+13
    assume {:print "$at(28,687,700)"} true;
    $t3 := $1_string_String($t0);

    // trace_return[0]($t3) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:20:9+13
    assume {:print "$track_return(3,13,0):", $t3} $t3 == $t3;

    // label L3 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:21:5+1
    assume {:print "$at(28,705,706)"} true;
L3:

    // return $t3 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:21:5+1
    assume {:print "$at(28,705,706)"} true;
    $ret0 := $t3;
    return;

    // label L4 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:21:5+1
L4:

    // abort($t2) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/../move-stdlib/sources/string.move:21:5+1
    assume {:print "$at(28,705,706)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// spec fun at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.spec.move:54:10+120
function  $1_string_utils_spec_native_format'bool'(s: bool, type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool): $1_string_String;
axiom (forall s: bool, type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool ::
(var $$res := $1_string_utils_spec_native_format'bool'(s, type_tag, canonicalize, single_line, include_int_types);
$IsValid'$1_string_String'($$res)));

// spec fun at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.spec.move:54:10+120
function  $1_string_utils_spec_native_format'u8'(s: int, type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool): $1_string_String;
axiom (forall s: int, type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool ::
(var $$res := $1_string_utils_spec_native_format'u8'(s, type_tag, canonicalize, single_line, include_int_types);
$IsValid'$1_string_String'($$res)));

// spec fun at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.spec.move:54:10+120
function  $1_string_utils_spec_native_format'u64'(s: int, type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool): $1_string_String;
axiom (forall s: int, type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool ::
(var $$res := $1_string_utils_spec_native_format'u64'(s, type_tag, canonicalize, single_line, include_int_types);
$IsValid'$1_string_String'($$res)));

// spec fun at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.spec.move:54:10+120
function  $1_string_utils_spec_native_format'vec'u8''(s: Vec (int), type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool): $1_string_String;
axiom (forall s: Vec (int), type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool ::
(var $$res := $1_string_utils_spec_native_format'vec'u8''(s, type_tag, canonicalize, single_line, include_int_types);
$IsValid'$1_string_String'($$res)));

// spec fun at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.spec.move:54:10+120
function  $1_string_utils_spec_native_format'$1_string_String'(s: $1_string_String, type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool): $1_string_String;
axiom (forall s: $1_string_String, type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool ::
(var $$res := $1_string_utils_spec_native_format'$1_string_String'(s, type_tag, canonicalize, single_line, include_int_types);
$IsValid'$1_string_String'($$res)));

// spec fun at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.spec.move:54:10+120
function  $1_string_utils_spec_native_format'$42_Generics_Flexy'u8''(s: $42_Generics_Flexy'u8', type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool): $1_string_String;
axiom (forall s: $42_Generics_Flexy'u8', type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool ::
(var $$res := $1_string_utils_spec_native_format'$42_Generics_Flexy'u8''(s, type_tag, canonicalize, single_line, include_int_types);
$IsValid'$1_string_String'($$res)));

// spec fun at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.spec.move:54:10+120
function  $1_string_utils_spec_native_format'$42_simple12_Info'(s: $42_simple12_Info, type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool): $1_string_String;
axiom (forall s: $42_simple12_Info, type_tag: bool, canonicalize: bool, single_line: bool, include_int_types: bool ::
(var $$res := $1_string_utils_spec_native_format'$42_simple12_Info'(s, type_tag, canonicalize, single_line, include_int_types);
$IsValid'$1_string_String'($$res)));

// fun string_utils::debug_string<bool> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+101
procedure {:inline 1} $1_string_utils_debug_string'bool'(_$t0: bool) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: bool;
    var $t2: bool;
    var $t3: bool;
    var $t4: bool;
    var $t5: $1_string_String;
    var $t0: bool;
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'bool': bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+1
    assume {:print "$at(87,1620,1621)"} true;
    assume {:print "$track_local(4,1,0):", $t0} $t0 == $t0;

    // $t1 := true at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:26+4
    assume {:print "$at(87,1689,1693)"} true;
    $t1 := true;
    assume $IsValid'bool'($t1);

    // $t2 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:32+5
    $t2 := false;
    assume $IsValid'bool'($t2);

    // $t3 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:39+5
    $t3 := false;
    assume $IsValid'bool'($t3);

    // $t4 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:46+5
    $t4 := false;
    assume $IsValid'bool'($t4);

    // $t5 := opaque begin: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // assume WellFormed($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsValid'$1_string_String'($t5);

    // assume Eq<string::String>($t5, string_utils::spec_native_format<#0>($t0, $t1, $t2, $t3, $t4)) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsEqual'$1_string_String'($t5, $1_string_utils_spec_native_format'bool'($t0, $t1, $t2, $t3, $t4));

    // $t5 := opaque end: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // trace_return[0]($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume {:print "$track_return(4,1,0):", $t5} $t5 == $t5;

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
L1:

    // return $t5 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
    $ret0 := $t5;
    return;

}

// fun string_utils::debug_string<u8> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+101
procedure {:inline 1} $1_string_utils_debug_string'u8'(_$t0: int) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: bool;
    var $t2: bool;
    var $t3: bool;
    var $t4: bool;
    var $t5: $1_string_String;
    var $t0: int;
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'u8': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+1
    assume {:print "$at(87,1620,1621)"} true;
    assume {:print "$track_local(4,1,0):", $t0} $t0 == $t0;

    // $t1 := true at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:26+4
    assume {:print "$at(87,1689,1693)"} true;
    $t1 := true;
    assume $IsValid'bool'($t1);

    // $t2 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:32+5
    $t2 := false;
    assume $IsValid'bool'($t2);

    // $t3 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:39+5
    $t3 := false;
    assume $IsValid'bool'($t3);

    // $t4 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:46+5
    $t4 := false;
    assume $IsValid'bool'($t4);

    // $t5 := opaque begin: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // assume WellFormed($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsValid'$1_string_String'($t5);

    // assume Eq<string::String>($t5, string_utils::spec_native_format<#0>($t0, $t1, $t2, $t3, $t4)) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsEqual'$1_string_String'($t5, $1_string_utils_spec_native_format'u8'($t0, $t1, $t2, $t3, $t4));

    // $t5 := opaque end: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // trace_return[0]($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume {:print "$track_return(4,1,0):", $t5} $t5 == $t5;

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
L1:

    // return $t5 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
    $ret0 := $t5;
    return;

}

// fun string_utils::debug_string<u64> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+101
procedure {:inline 1} $1_string_utils_debug_string'u64'(_$t0: int) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: bool;
    var $t2: bool;
    var $t3: bool;
    var $t4: bool;
    var $t5: $1_string_String;
    var $t0: int;
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+1
    assume {:print "$at(87,1620,1621)"} true;
    assume {:print "$track_local(4,1,0):", $t0} $t0 == $t0;

    // $t1 := true at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:26+4
    assume {:print "$at(87,1689,1693)"} true;
    $t1 := true;
    assume $IsValid'bool'($t1);

    // $t2 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:32+5
    $t2 := false;
    assume $IsValid'bool'($t2);

    // $t3 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:39+5
    $t3 := false;
    assume $IsValid'bool'($t3);

    // $t4 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:46+5
    $t4 := false;
    assume $IsValid'bool'($t4);

    // $t5 := opaque begin: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // assume WellFormed($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsValid'$1_string_String'($t5);

    // assume Eq<string::String>($t5, string_utils::spec_native_format<#0>($t0, $t1, $t2, $t3, $t4)) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsEqual'$1_string_String'($t5, $1_string_utils_spec_native_format'u64'($t0, $t1, $t2, $t3, $t4));

    // $t5 := opaque end: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // trace_return[0]($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume {:print "$track_return(4,1,0):", $t5} $t5 == $t5;

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
L1:

    // return $t5 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
    $ret0 := $t5;
    return;

}

// fun string_utils::debug_string<vector<u8>> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+101
procedure {:inline 1} $1_string_utils_debug_string'vec'u8''(_$t0: Vec (int)) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: bool;
    var $t2: bool;
    var $t3: bool;
    var $t4: bool;
    var $t5: $1_string_String;
    var $t0: Vec (int);
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+1
    assume {:print "$at(87,1620,1621)"} true;
    assume {:print "$track_local(4,1,0):", $t0} $t0 == $t0;

    // $t1 := true at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:26+4
    assume {:print "$at(87,1689,1693)"} true;
    $t1 := true;
    assume $IsValid'bool'($t1);

    // $t2 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:32+5
    $t2 := false;
    assume $IsValid'bool'($t2);

    // $t3 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:39+5
    $t3 := false;
    assume $IsValid'bool'($t3);

    // $t4 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:46+5
    $t4 := false;
    assume $IsValid'bool'($t4);

    // $t5 := opaque begin: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // assume WellFormed($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsValid'$1_string_String'($t5);

    // assume Eq<string::String>($t5, string_utils::spec_native_format<#0>($t0, $t1, $t2, $t3, $t4)) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsEqual'$1_string_String'($t5, $1_string_utils_spec_native_format'vec'u8''($t0, $t1, $t2, $t3, $t4));

    // $t5 := opaque end: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // trace_return[0]($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume {:print "$track_return(4,1,0):", $t5} $t5 == $t5;

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
L1:

    // return $t5 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
    $ret0 := $t5;
    return;

}

// fun string_utils::debug_string<string::String> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+101
procedure {:inline 1} $1_string_utils_debug_string'$1_string_String'(_$t0: $1_string_String) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: bool;
    var $t2: bool;
    var $t3: bool;
    var $t4: bool;
    var $t5: $1_string_String;
    var $t0: $1_string_String;
    var $temp_0'$1_string_String': $1_string_String;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+1
    assume {:print "$at(87,1620,1621)"} true;
    assume {:print "$track_local(4,1,0):", $t0} $t0 == $t0;

    // $t1 := true at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:26+4
    assume {:print "$at(87,1689,1693)"} true;
    $t1 := true;
    assume $IsValid'bool'($t1);

    // $t2 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:32+5
    $t2 := false;
    assume $IsValid'bool'($t2);

    // $t3 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:39+5
    $t3 := false;
    assume $IsValid'bool'($t3);

    // $t4 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:46+5
    $t4 := false;
    assume $IsValid'bool'($t4);

    // $t5 := opaque begin: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // assume WellFormed($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsValid'$1_string_String'($t5);

    // assume Eq<string::String>($t5, string_utils::spec_native_format<#0>($t0, $t1, $t2, $t3, $t4)) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsEqual'$1_string_String'($t5, $1_string_utils_spec_native_format'$1_string_String'($t0, $t1, $t2, $t3, $t4));

    // $t5 := opaque end: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // trace_return[0]($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume {:print "$track_return(4,1,0):", $t5} $t5 == $t5;

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
L1:

    // return $t5 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
    $ret0 := $t5;
    return;

}

// fun string_utils::debug_string<Generics::Flexy<u8>> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+101
procedure {:inline 1} $1_string_utils_debug_string'$42_Generics_Flexy'u8''(_$t0: $42_Generics_Flexy'u8') returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: bool;
    var $t2: bool;
    var $t3: bool;
    var $t4: bool;
    var $t5: $1_string_String;
    var $t0: $42_Generics_Flexy'u8';
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'$42_Generics_Flexy'u8'': $42_Generics_Flexy'u8';
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+1
    assume {:print "$at(87,1620,1621)"} true;
    assume {:print "$track_local(4,1,0):", $t0} $t0 == $t0;

    // $t1 := true at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:26+4
    assume {:print "$at(87,1689,1693)"} true;
    $t1 := true;
    assume $IsValid'bool'($t1);

    // $t2 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:32+5
    $t2 := false;
    assume $IsValid'bool'($t2);

    // $t3 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:39+5
    $t3 := false;
    assume $IsValid'bool'($t3);

    // $t4 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:46+5
    $t4 := false;
    assume $IsValid'bool'($t4);

    // $t5 := opaque begin: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // assume WellFormed($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsValid'$1_string_String'($t5);

    // assume Eq<string::String>($t5, string_utils::spec_native_format<#0>($t0, $t1, $t2, $t3, $t4)) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsEqual'$1_string_String'($t5, $1_string_utils_spec_native_format'$42_Generics_Flexy'u8''($t0, $t1, $t2, $t3, $t4));

    // $t5 := opaque end: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // trace_return[0]($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume {:print "$track_return(4,1,0):", $t5} $t5 == $t5;

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
L1:

    // return $t5 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
    $ret0 := $t5;
    return;

}

// fun string_utils::debug_string<simple12::Info> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+101
procedure {:inline 1} $1_string_utils_debug_string'$42_simple12_Info'(_$t0: $42_simple12_Info) returns ($ret0: $1_string_String)
{
    // declare local variables
    var $t1: bool;
    var $t2: bool;
    var $t3: bool;
    var $t4: bool;
    var $t5: $1_string_String;
    var $t0: $42_simple12_Info;
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'$42_simple12_Info': $42_simple12_Info;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:34:5+1
    assume {:print "$at(87,1620,1621)"} true;
    assume {:print "$track_local(4,1,0):", $t0} $t0 == $t0;

    // $t1 := true at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:26+4
    assume {:print "$at(87,1689,1693)"} true;
    $t1 := true;
    assume $IsValid'bool'($t1);

    // $t2 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:32+5
    $t2 := false;
    assume $IsValid'bool'($t2);

    // $t3 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:39+5
    $t3 := false;
    assume $IsValid'bool'($t3);

    // $t4 := false at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:46+5
    $t4 := false;
    assume $IsValid'bool'($t4);

    // $t5 := opaque begin: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // assume WellFormed($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsValid'$1_string_String'($t5);

    // assume Eq<string::String>($t5, string_utils::spec_native_format<#0>($t0, $t1, $t2, $t3, $t4)) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume $IsEqual'$1_string_String'($t5, $1_string_utils_spec_native_format'$42_simple12_Info'($t0, $t1, $t2, $t3, $t4));

    // $t5 := opaque end: string_utils::native_format<#0>($t0, $t1, $t2, $t3, $t4) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43

    // trace_return[0]($t5) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:35:9+43
    assume {:print "$track_return(4,1,0):", $t5} $t5 == $t5;

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
L1:

    // return $t5 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/string_utils.move:36:5+1
    assume {:print "$at(87,1720,1721)"} true;
    $ret0 := $t5;
    return;

}

// fun debug::print<bool> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+67
procedure {:inline 1} $1_debug_print'bool'(_$t0: bool) returns ()
{
    // declare local variables
    var $t1: $1_string_String;
    var $t2: int;
    var $t0: bool;
    var $temp_0'bool': bool;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[x]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+1
    assume {:print "$at(68,102,103)"} true;
    assume {:print "$track_local(5,2,0):", $t0} $t0 == $t0;

    // $t1 := string_utils::debug_string<#0>($t0) on_abort goto L2 with $t2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:14:9+40
    assume {:print "$at(68,309,349)"} true;
    call $t1 := $1_string_utils_debug_string'bool'($t0);
    if ($abort_flag) {
        assume {:print "$at(68,309,349)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(5,2):", $t2} $t2 == $t2;
        goto L2;
    }

    // opaque begin: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23
    assume {:print "$at(68,139,162)"} true;

    // opaque end: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
L1:

    // return () at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    return;

    // label L2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
L2:

    // abort($t2) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun debug::print<u8> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+67
procedure {:inline 1} $1_debug_print'u8'(_$t0: bv8) returns ()
{
    // declare local variables
    var $t1: $1_string_String;
    var $t2: int;
    var $t0: bv8;
    var $temp_0'bv8': bv8;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[x]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+1
    assume {:print "$at(68,102,103)"} true;
    assume {:print "$track_local(5,2,0):", $t0} $t0 == $t0;

    // $t1 := string_utils::debug_string<#0>($t0) on_abort goto L2 with $t2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:14:9+40
    assume {:print "$at(68,309,349)"} true;
    call $t1 := $1_string_utils_debug_string'u8'($t0);
    if ($abort_flag) {
        assume {:print "$at(68,309,349)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(5,2):", $t2} $t2 == $t2;
        goto L2;
    }

    // opaque begin: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23
    assume {:print "$at(68,139,162)"} true;

    // opaque end: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
L1:

    // return () at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    return;

    // label L2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
L2:

    // abort($t2) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun debug::print<u64> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+67
procedure {:inline 1} $1_debug_print'u64'(_$t0: bv64) returns ()
{
    // declare local variables
    var $t1: $1_string_String;
    var $t2: int;
    var $t0: bv64;
    var $temp_0'bv64': bv64;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[x]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+1
    assume {:print "$at(68,102,103)"} true;
    assume {:print "$track_local(5,2,0):", $t0} $t0 == $t0;

    // $t1 := string_utils::debug_string<#0>($t0) on_abort goto L2 with $t2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:14:9+40
    assume {:print "$at(68,309,349)"} true;
    call $t1 := $1_string_utils_debug_string'u64'($t0);
    if ($abort_flag) {
        assume {:print "$at(68,309,349)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(5,2):", $t2} $t2 == $t2;
        goto L2;
    }

    // opaque begin: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23
    assume {:print "$at(68,139,162)"} true;

    // opaque end: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
L1:

    // return () at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    return;

    // label L2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
L2:

    // abort($t2) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun debug::print<vector<u8>> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+67
procedure {:inline 1} $1_debug_print'vec'u8''(_$t0: Vec (bv8)) returns ()
{
    // declare local variables
    var $t1: $1_string_String;
    var $t2: int;
    var $t0: Vec (bv8);
    var $temp_0'vec'bv8'': Vec (bv8);
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[x]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+1
    assume {:print "$at(68,102,103)"} true;
    assume {:print "$track_local(5,2,0):", $t0} $t0 == $t0;

    // $t1 := string_utils::debug_string<#0>($t0) on_abort goto L2 with $t2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:14:9+40
    assume {:print "$at(68,309,349)"} true;
    call $t1 := $1_string_utils_debug_string'vec'u8''($t0);
    if ($abort_flag) {
        assume {:print "$at(68,309,349)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(5,2):", $t2} $t2 == $t2;
        goto L2;
    }

    // opaque begin: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23
    assume {:print "$at(68,139,162)"} true;

    // opaque end: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
L1:

    // return () at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    return;

    // label L2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
L2:

    // abort($t2) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun debug::print<string::String> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+67
procedure {:inline 1} $1_debug_print'$1_string_String'(_$t0: $1_string_String) returns ()
{
    // declare local variables
    var $t1: $1_string_String;
    var $t2: int;
    var $t0: $1_string_String;
    var $temp_0'$1_string_String': $1_string_String;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[x]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+1
    assume {:print "$at(68,102,103)"} true;
    assume {:print "$track_local(5,2,0):", $t0} $t0 == $t0;

    // $t1 := string_utils::debug_string<#0>($t0) on_abort goto L2 with $t2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:14:9+40
    assume {:print "$at(68,309,349)"} true;
    call $t1 := $1_string_utils_debug_string'$1_string_String'($t0);
    if ($abort_flag) {
        assume {:print "$at(68,309,349)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(5,2):", $t2} $t2 == $t2;
        goto L2;
    }

    // opaque begin: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23
    assume {:print "$at(68,139,162)"} true;

    // opaque end: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
L1:

    // return () at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    return;

    // label L2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
L2:

    // abort($t2) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun debug::print<Generics::Flexy<u8>> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+67
procedure {:inline 1} $1_debug_print'$42_Generics_Flexy'u8''(_$t0: $42_Generics_Flexy'u8') returns ()
{
    // declare local variables
    var $t1: $1_string_String;
    var $t2: int;
    var $t0: $42_Generics_Flexy'u8';
    var $temp_0'$42_Generics_Flexy'u8'': $42_Generics_Flexy'u8';
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[x]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+1
    assume {:print "$at(68,102,103)"} true;
    assume {:print "$track_local(5,2,0):", $t0} $t0 == $t0;

    // $t1 := string_utils::debug_string<#0>($t0) on_abort goto L2 with $t2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:14:9+40
    assume {:print "$at(68,309,349)"} true;
    call $t1 := $1_string_utils_debug_string'$42_Generics_Flexy'u8''($t0);
    if ($abort_flag) {
        assume {:print "$at(68,309,349)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(5,2):", $t2} $t2 == $t2;
        goto L2;
    }

    // opaque begin: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23
    assume {:print "$at(68,139,162)"} true;

    // opaque end: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
L1:

    // return () at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    return;

    // label L2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
L2:

    // abort($t2) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun debug::print<simple12::Info> [baseline] at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+67
procedure {:inline 1} $1_debug_print'$42_simple12_Info'(_$t0: $42_simple12_Info) returns ()
{
    // declare local variables
    var $t1: $1_string_String;
    var $t2: int;
    var $t0: $42_simple12_Info;
    var $temp_0'$42_simple12_Info': $42_simple12_Info;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[x]($t0) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:5:5+1
    assume {:print "$at(68,102,103)"} true;
    assume {:print "$track_local(5,2,0):", $t0} $t0 == $t0;

    // $t1 := string_utils::debug_string<#0>($t0) on_abort goto L2 with $t2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:14:9+40
    assume {:print "$at(68,309,349)"} true;
    call $t1 := $1_string_utils_debug_string'$42_simple12_Info'($t0);
    if ($abort_flag) {
        assume {:print "$at(68,309,349)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(5,2):", $t2} $t2 == $t2;
        goto L2;
    }

    // opaque begin: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23
    assume {:print "$at(68,139,162)"} true;

    // opaque end: debug::native_print($t1) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:6:9+23

    // label L1 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
L1:

    // return () at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    return;

    // label L2 at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
L2:

    // abort($t2) at /home/unnamed/.move/https___github_com_aptos-labs_aptos-core_git_mainnet/aptos-move/framework/aptos-framework/../aptos-stdlib/sources/debug.move:7:5+1
    assume {:print "$at(68,168,169)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun PriceOracle::get_price [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple8.move:4:9+67
procedure {:inline 1} $42_PriceOracle_get_price() returns ($ret0: int)
{
    // declare local variables
    var $t0: int;
    var $temp_0'u128': int;

    // bytecode translation starts here
    // $t0 := 54200 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:5:20+5
    assume {:print "$at(15,107,112)"} true;
    $t0 := 54200;
    assume $IsValid'u128'($t0);

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple8.move:5:13+12
    assume {:print "$track_return(6,0,0):", $t0} $t0 == $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:6:9+1
    assume {:print "$at(15,122,123)"} true;
L1:

    // return $t0 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:6:9+1
    assume {:print "$at(15,122,123)"} true;
    $ret0 := $t0;
    return;

}

// fun PriceOracle::get_price [verification] at /mnt/c/Users/DELL/move-tut/sources/simple8.move:4:9+67
procedure {:timeLimit 40} $42_PriceOracle_get_price$verify() returns ($ret0: int)
{
    // declare local variables
    var $t0: int;
    var $temp_0'u128': int;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := 54200 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:5:20+5
    assume {:print "$at(15,107,112)"} true;
    $t0 := 54200;
    assume $IsValid'u128'($t0);

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple8.move:5:13+12
    assume {:print "$track_return(6,0,0):", $t0} $t0 == $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:6:9+1
    assume {:print "$at(15,122,123)"} true;
L1:

    // return $t0 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:6:9+1
    assume {:print "$at(15,122,123)"} true;
    $ret0 := $t0;
    return;

}

// fun Casting::calc_swap [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple8.move:13:9+215
procedure {:inline 1} $42_Casting_calc_swap() returns ($ret0: int)
{
    // declare local variables
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $temp_0'u64': int;

    // bytecode translation starts here
    // $t0 := PriceOracle::get_price() on_abort goto L2 with $t1 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:14:25+24
    assume {:print "$at(15,283,307)"} true;
    call $t0 := $42_PriceOracle_get_price();
    if ($abort_flag) {
        assume {:print "$at(15,283,307)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(7,0):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := (u64)($t0) on_abort goto L2 with $t1 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:16:40+14
    assume {:print "$at(15,382,396)"} true;
    call $t2 := $CastU64($t0);
    if ($abort_flag) {
        assume {:print "$at(15,382,396)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(7,0):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := 100 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:15:28+3
    assume {:print "$at(15,337,340)"} true;
    $t3 := 100;
    assume $IsValid'u64'($t3);

    // $t4 := +($t2, $t3) on_abort goto L2 with $t1 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:16:55+1
    assume {:print "$at(15,397,398)"} true;
    call $t4 := $AddU64($t2, $t3);
    if ($abort_flag) {
        assume {:print "$at(15,397,398)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(7,0):", $t1} $t1 == $t1;
        goto L2;
    }

    // trace_return[0]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple8.move:17:13+21
    assume {:print "$at(15,417,438)"} true;
    assume {:print "$track_return(7,0,0):", $t4} $t4 == $t4;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:18:9+1
    assume {:print "$at(15,448,449)"} true;
L1:

    // return $t4 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:18:9+1
    assume {:print "$at(15,448,449)"} true;
    $ret0 := $t4;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:18:9+1
L2:

    // abort($t1) at /mnt/c/Users/DELL/move-tut/sources/simple8.move:18:9+1
    assume {:print "$at(15,448,449)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun Casting::calc_swap [verification] at /mnt/c/Users/DELL/move-tut/sources/simple8.move:13:9+215
procedure {:timeLimit 40} $42_Casting_calc_swap$verify() returns ($ret0: int)
{
    // declare local variables
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $temp_0'u64': int;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := PriceOracle::get_price() on_abort goto L2 with $t1 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:14:25+24
    assume {:print "$at(15,283,307)"} true;
    call $t0 := $42_PriceOracle_get_price();
    if ($abort_flag) {
        assume {:print "$at(15,283,307)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(7,0):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := (u64)($t0) on_abort goto L2 with $t1 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:16:40+14
    assume {:print "$at(15,382,396)"} true;
    call $t2 := $CastU64($t0);
    if ($abort_flag) {
        assume {:print "$at(15,382,396)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(7,0):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := 100 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:15:28+3
    assume {:print "$at(15,337,340)"} true;
    $t3 := 100;
    assume $IsValid'u64'($t3);

    // $t4 := +($t2, $t3) on_abort goto L2 with $t1 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:16:55+1
    assume {:print "$at(15,397,398)"} true;
    call $t4 := $AddU64($t2, $t3);
    if ($abort_flag) {
        assume {:print "$at(15,397,398)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(7,0):", $t1} $t1 == $t1;
        goto L2;
    }

    // trace_return[0]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple8.move:17:13+21
    assume {:print "$at(15,417,438)"} true;
    assume {:print "$track_return(7,0,0):", $t4} $t4 == $t4;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:18:9+1
    assume {:print "$at(15,448,449)"} true;
L1:

    // return $t4 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:18:9+1
    assume {:print "$at(15,448,449)"} true;
    $ret0 := $t4;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:18:9+1
L2:

    // abort($t1) at /mnt/c/Users/DELL/move-tut/sources/simple8.move:18:9+1
    assume {:print "$at(15,448,449)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun Casting::test_calc_swap [verification] at /mnt/c/Users/DELL/move-tut/sources/simple8.move:21:9+116
procedure {:timeLimit 40} $42_Casting_test_calc_swap$verify() returns ()
{
    // declare local variables
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $temp_0'u64': int;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t1 := Casting::calc_swap() on_abort goto L2 with $t2 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:22:34+11
    assume {:print "$at(15,537,548)"} true;
    call $t1 := $42_Casting_calc_swap();
    if ($abort_flag) {
        assume {:print "$at(15,537,548)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(7,1):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_local[price_with_fee]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple8.move:22:17+14
    assume {:print "$track_local(7,1,0):", $t1} $t1 == $t1;

    // debug::print<u64>($t1) on_abort goto L2 with $t2 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:23:13+22
    assume {:print "$at(15,563,585)"} true;
    call $1_debug_print'u64'($t1);
    if ($abort_flag) {
        assume {:print "$at(15,563,585)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(7,1):", $t2} $t2 == $t2;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:24:9+1
    assume {:print "$at(15,596,597)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple8.move:24:9+1
    assume {:print "$at(15,596,597)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple8.move:24:9+1
L2:

    // abort($t2) at /mnt/c/Users/DELL/move-tut/sources/simple8.move:24:9+1
    assume {:print "$at(15,596,597)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// struct Generics::Flexy<u8> at /mnt/c/Users/DELL/move-tut/sources/simple14.move:4:5+73
datatype $42_Generics_Flexy'u8' {
    $42_Generics_Flexy'u8'($x: int)
}
function {:inline} $Update'$42_Generics_Flexy'u8''_x(s: $42_Generics_Flexy'u8', x: int): $42_Generics_Flexy'u8' {
    $42_Generics_Flexy'u8'(x)
}
function $IsValid'$42_Generics_Flexy'u8''(s: $42_Generics_Flexy'u8'): bool {
    $IsValid'u8'(s->$x)
}
function {:inline} $IsEqual'$42_Generics_Flexy'u8''(s1: $42_Generics_Flexy'u8', s2: $42_Generics_Flexy'u8'): bool {
    s1 == s2
}

// fun Generics::new_flexi [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple14.move:8:5+96
procedure {:inline 1} $42_Generics_new_flexi(_$t0: int) returns ($ret0: $42_Generics_Flexy'u8')
{
    // declare local variables
    var $t1: $42_Generics_Flexy'u8';
    var $t0: int;
    var $temp_0'$42_Generics_Flexy'u8'': $42_Generics_Flexy'u8';
    var $temp_0'u8': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[_x]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple14.move:8:5+1
    assume {:print "$at(8,141,142)"} true;
    assume {:print "$track_local(8,0,0):", $t0} $t0 == $t0;

    // $t1 := pack Generics::Flexy<u8>($t0) at /mnt/c/Users/DELL/move-tut/sources/simple14.move:9:16+38
    assume {:print "$at(8,192,230)"} true;
    $t1 := $42_Generics_Flexy'u8'($t0);

    // trace_return[0]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple14.move:9:9+45
    assume {:print "$track_return(8,0,0):", $t1} $t1 == $t1;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple14.move:12:5+1
    assume {:print "$at(8,236,237)"} true;
L1:

    // return $t1 at /mnt/c/Users/DELL/move-tut/sources/simple14.move:12:5+1
    assume {:print "$at(8,236,237)"} true;
    $ret0 := $t1;
    return;

}

// fun Generics::new_flexi [verification] at /mnt/c/Users/DELL/move-tut/sources/simple14.move:8:5+96
procedure {:timeLimit 40} $42_Generics_new_flexi$verify(_$t0: int) returns ($ret0: $42_Generics_Flexy'u8')
{
    // declare local variables
    var $t1: $42_Generics_Flexy'u8';
    var $t0: int;
    var $temp_0'$42_Generics_Flexy'u8'': $42_Generics_Flexy'u8';
    var $temp_0'u8': int;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple14.move:8:5+1
    assume {:print "$at(8,141,142)"} true;
    assume $IsValid'u8'($t0);

    // trace_local[_x]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple14.move:8:5+1
    assume {:print "$track_local(8,0,0):", $t0} $t0 == $t0;

    // $t1 := pack Generics::Flexy<u8>($t0) at /mnt/c/Users/DELL/move-tut/sources/simple14.move:9:16+38
    assume {:print "$at(8,192,230)"} true;
    $t1 := $42_Generics_Flexy'u8'($t0);

    // trace_return[0]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple14.move:9:9+45
    assume {:print "$track_return(8,0,0):", $t1} $t1 == $t1;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple14.move:12:5+1
    assume {:print "$at(8,236,237)"} true;
L1:

    // return $t1 at /mnt/c/Users/DELL/move-tut/sources/simple14.move:12:5+1
    assume {:print "$at(8,236,237)"} true;
    $ret0 := $t1;
    return;

}

// fun Generics::test_flex [verification] at /mnt/c/Users/DELL/move-tut/sources/simple14.move:15:5+87
procedure {:timeLimit 40} $42_Generics_test_flex$verify() returns ()
{
    // declare local variables
    var $t0: $42_Generics_Flexy'u8';
    var $t1: int;
    var $t2: $42_Generics_Flexy'u8';
    var $t3: int;
    var $temp_0'$42_Generics_Flexy'u8'': $42_Generics_Flexy'u8';

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t1 := 10 at /mnt/c/Users/DELL/move-tut/sources/simple14.move:17:27+2
    assume {:print "$at(8,308,310)"} true;
    $t1 := 10;
    assume $IsValid'u8'($t1);

    // $t2 := Generics::new_flexi($t1) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple14.move:17:17+13
    call $t2 := $42_Generics_new_flexi($t1);
    if ($abort_flag) {
        assume {:print "$at(8,298,311)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(8,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_local[f]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple14.move:17:13+1
    assume {:print "$track_local(8,1,0):", $t2} $t2 == $t2;

    // debug::print<Generics::Flexy<u8>>($t2) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple14.move:18:9+16
    assume {:print "$at(8,322,338)"} true;
    call $1_debug_print'$42_Generics_Flexy'u8''($t2);
    if ($abort_flag) {
        assume {:print "$at(8,322,338)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(8,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple14.move:20:1+1
    assume {:print "$at(8,347,348)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple14.move:20:1+1
    assume {:print "$at(8,347,348)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple14.move:20:1+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple14.move:20:1+1
    assume {:print "$at(8,347,348)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun Liquidity_pool_calculator::calculate_swap [baseline] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:65:5+368
procedure {:inline 1} $42_Liquidity_pool_calculator_calculate_swap(_$t0: int, _$t1: int, _$t2: int) returns ($ret0: int)
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: bool;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[coin1]($t0) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:65:5+1
    assume {:print "$at(2,1689,1690)"} true;
    assume {:print "$track_local(9,0,0):", $t0} $t0 == $t0;

    // trace_local[coin2]($t1) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:65:5+1
    assume {:print "$track_local(9,0,1):", $t1} $t1 == $t1;

    // trace_local[coin1_amt]($t2) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:65:5+1
    assume {:print "$track_local(9,0,2):", $t2} $t2 == $t2;

    // $t7 := 0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:29+1
    assume {:print "$at(2,1784,1785)"} true;
    $t7 := 0;
    assume $IsValid'u64'($t7);

    // $t8 := >($t2, $t7) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:27+1
    call $t8 := $Gt($t2, $t7);

    // if ($t8) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:9+35
    if ($t8) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:9+35
L1:

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:9+35
    assume {:print "$at(2,1764,1799)"} true;
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:32+11
L0:

    // $t9 := 0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:32+11
    assume {:print "$at(2,1787,1798)"} true;
    $t9 := 0;
    assume $IsValid'u64'($t9);

    // trace_abort($t9) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:9+35
    assume {:print "$at(2,1764,1799)"} true;
    assume {:print "$track_abort(9,0):", $t9} $t9 == $t9;

    // $t10 := move($t9) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:9+35
    $t10 := $t9;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:9+35
    goto L4;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:67:19+9
    assume {:print "$at(2,1820,1829)"} true;
L2:

    // $t11 := 5 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:67:31+1
    assume {:print "$at(2,1832,1833)"} true;
    $t11 := 5;
    assume $IsValid'u64'($t11);

    // $t12 := *($t2, $t11) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:67:29+1
    call $t12 := $MulU64($t2, $t11);
    if ($abort_flag) {
        assume {:print "$at(2,1830,1831)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // $t13 := 1000 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:67:35+4
    $t13 := 1000;
    assume $IsValid'u64'($t13);

    // $t14 := /($t12, $t13) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:67:33+1
    call $t14 := $Div($t12, $t13);
    if ($abort_flag) {
        assume {:print "$at(2,1834,1835)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[fee]($t14) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:67:13+3
    assume {:print "$track_local(9,0,3):", $t14} $t14 == $t14;

    // $t15 := *($t0, $t1) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:68:37+1
    assume {:print "$at(2,1879,1880)"} true;
    call $t15 := $MulU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,1879,1880)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[mix_supply]($t15) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:68:13+10
    assume {:print "$track_local(9,0,4):", $t15} $t15 == $t15;

    // $t16 := +($t0, $t2) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:69:30+1
    assume {:print "$at(2,1918,1919)"} true;
    call $t16 := $AddU64($t0, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,1918,1919)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[new_usdt]($t16) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:69:13+8
    assume {:print "$track_local(9,0,6):", $t16} $t16 == $t16;

    // $t17 := -($t16, $t14) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:70:47+1
    assume {:print "$at(2,1978,1979)"} true;
    call $t17 := $Sub($t16, $t14);
    if ($abort_flag) {
        assume {:print "$at(2,1978,1979)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // $t18 := /($t15, $t17) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:70:35+1
    call $t18 := $Div($t15, $t17);
    if ($abort_flag) {
        assume {:print "$at(2,1966,1967)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[new_n2dr]($t18) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:70:13+8
    assume {:print "$track_local(9,0,5):", $t18} $t18 == $t18;

    // $t19 := -($t1, $t18) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:71:29+1
    assume {:print "$at(2,2015,2016)"} true;
    call $t19 := $Sub($t1, $t18);
    if ($abort_flag) {
        assume {:print "$at(2,2015,2016)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_return[0]($t19) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:72:9+14
    assume {:print "$at(2,2036,2050)"} true;
    assume {:print "$track_return(9,0,0):", $t19} $t19 == $t19;

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:73:5+1
    assume {:print "$at(2,2056,2057)"} true;
L3:

    // return $t19 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:73:5+1
    assume {:print "$at(2,2056,2057)"} true;
    $ret0 := $t19;
    return;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:73:5+1
L4:

    // abort($t10) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:73:5+1
    assume {:print "$at(2,2056,2057)"} true;
    $abort_code := $t10;
    $abort_flag := true;
    return;

}

// fun Liquidity_pool_calculator::calculate_swap [verification] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:65:5+368
procedure {:timeLimit 40} $42_Liquidity_pool_calculator_calculate_swap$verify(_$t0: int, _$t1: int, _$t2: int) returns ($ret0: int)
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: bool;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:65:5+1
    assume {:print "$at(2,1689,1690)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:65:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:65:5+1
    assume $IsValid'u64'($t2);

    // trace_local[coin1]($t0) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:65:5+1
    assume {:print "$track_local(9,0,0):", $t0} $t0 == $t0;

    // trace_local[coin2]($t1) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:65:5+1
    assume {:print "$track_local(9,0,1):", $t1} $t1 == $t1;

    // trace_local[coin1_amt]($t2) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:65:5+1
    assume {:print "$track_local(9,0,2):", $t2} $t2 == $t2;

    // $t7 := 0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:29+1
    assume {:print "$at(2,1784,1785)"} true;
    $t7 := 0;
    assume $IsValid'u64'($t7);

    // $t8 := >($t2, $t7) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:27+1
    call $t8 := $Gt($t2, $t7);

    // if ($t8) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:9+35
    if ($t8) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:9+35
L1:

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:9+35
    assume {:print "$at(2,1764,1799)"} true;
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:32+11
L0:

    // $t9 := 0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:32+11
    assume {:print "$at(2,1787,1798)"} true;
    $t9 := 0;
    assume $IsValid'u64'($t9);

    // trace_abort($t9) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:9+35
    assume {:print "$at(2,1764,1799)"} true;
    assume {:print "$track_abort(9,0):", $t9} $t9 == $t9;

    // $t10 := move($t9) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:9+35
    $t10 := $t9;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:66:9+35
    goto L4;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:67:19+9
    assume {:print "$at(2,1820,1829)"} true;
L2:

    // $t11 := 5 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:67:31+1
    assume {:print "$at(2,1832,1833)"} true;
    $t11 := 5;
    assume $IsValid'u64'($t11);

    // $t12 := *($t2, $t11) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:67:29+1
    call $t12 := $MulU64($t2, $t11);
    if ($abort_flag) {
        assume {:print "$at(2,1830,1831)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // $t13 := 1000 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:67:35+4
    $t13 := 1000;
    assume $IsValid'u64'($t13);

    // $t14 := /($t12, $t13) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:67:33+1
    call $t14 := $Div($t12, $t13);
    if ($abort_flag) {
        assume {:print "$at(2,1834,1835)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[fee]($t14) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:67:13+3
    assume {:print "$track_local(9,0,3):", $t14} $t14 == $t14;

    // $t15 := *($t0, $t1) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:68:37+1
    assume {:print "$at(2,1879,1880)"} true;
    call $t15 := $MulU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,1879,1880)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[mix_supply]($t15) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:68:13+10
    assume {:print "$track_local(9,0,4):", $t15} $t15 == $t15;

    // $t16 := +($t0, $t2) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:69:30+1
    assume {:print "$at(2,1918,1919)"} true;
    call $t16 := $AddU64($t0, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,1918,1919)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[new_usdt]($t16) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:69:13+8
    assume {:print "$track_local(9,0,6):", $t16} $t16 == $t16;

    // $t17 := -($t16, $t14) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:70:47+1
    assume {:print "$at(2,1978,1979)"} true;
    call $t17 := $Sub($t16, $t14);
    if ($abort_flag) {
        assume {:print "$at(2,1978,1979)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // $t18 := /($t15, $t17) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:70:35+1
    call $t18 := $Div($t15, $t17);
    if ($abort_flag) {
        assume {:print "$at(2,1966,1967)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[new_n2dr]($t18) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:70:13+8
    assume {:print "$track_local(9,0,5):", $t18} $t18 == $t18;

    // $t19 := -($t1, $t18) on_abort goto L4 with $t10 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:71:29+1
    assume {:print "$at(2,2015,2016)"} true;
    call $t19 := $Sub($t1, $t18);
    if ($abort_flag) {
        assume {:print "$at(2,2015,2016)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(9,0):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_return[0]($t19) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:72:9+14
    assume {:print "$at(2,2036,2050)"} true;
    assume {:print "$track_return(9,0,0):", $t19} $t19 == $t19;

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:73:5+1
    assume {:print "$at(2,2056,2057)"} true;
L3:

    // return $t19 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:73:5+1
    assume {:print "$at(2,2056,2057)"} true;
    $ret0 := $t19;
    return;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:73:5+1
L4:

    // abort($t10) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:73:5+1
    assume {:print "$at(2,2056,2057)"} true;
    $abort_code := $t10;
    $abort_flag := true;
    return;

}

// fun Liquidity_pool_calculator::get_supply [baseline] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:48:5+317
procedure {:inline 1} $42_Liquidity_pool_calculator_get_supply(_$t0: int) returns ($ret0: int, $ret1: int, $ret2: Vec (int))
{
    // declare local variables
    var $t1: int;
    var $t2: bool;
    var $t3: int;
    var $t4: int;
    var $t5: Vec (int);
    var $t6: int;
    var $t7: int;
    var $t8: Vec (int);
    var $t9: int;
    var $t10: bool;
    var $t11: int;
    var $t12: int;
    var $t13: Vec (int);
    var $t14: int;
    var $t15: int;
    var $t16: Vec (int);
    var $t0: int;
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[coin_symbol]($t0) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:48:5+1
    assume {:print "$at(2,1140,1141)"} true;
    assume {:print "$track_local(9,1,0):", $t0} $t0 == $t0;

    // $t1 := 1 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:49:28+4
    assume {:print "$at(2,1227,1231)"} true;
    $t1 := 1;
    assume $IsValid'u64'($t1);

    // $t2 := ==($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:49:25+2
    $t2 := $IsEqual'u64'($t0, $t1);

    // if ($t2) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:49:9+242
    if ($t2) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:21+10
    assume {:print "$at(2,1254,1264)"} true;
L1:

    // $t3 := 3201 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:21+10
    assume {:print "$at(2,1254,1264)"} true;
    $t3 := 3201;
    assume $IsValid'u64'($t3);

    // $t4 := 312 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:33+10
    $t4 := 312;
    assume $IsValid'u64'($t4);

    // $t5 := [78, 50, 68, 32, 82, 101, 119, 97, 114, 100, 115] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:45+9
    $t5 := ConcatVec(ConcatVec(MakeVec4(78, 50, 68, 32), MakeVec4(82, 101, 119, 97)), MakeVec3(114, 100, 115));
    assume $IsValid'vec'u8''($t5);

    // trace_return[0]($t3) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    assume {:print "$track_return(9,1,0):", $t3} $t3 == $t3;

    // trace_return[1]($t4) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    assume {:print "$track_return(9,1,1):", $t4} $t4 == $t4;

    // trace_return[2]($t5) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    assume {:print "$track_return(9,1,2):", $t5} $t5 == $t5;

    // $t6 := move($t3) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    $t6 := $t3;

    // $t7 := move($t4) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    $t7 := $t4;

    // $t8 := move($t5) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    $t8 := $t5;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    goto L4;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:51:18+11
    assume {:print "$at(2,1307,1318)"} true;
L0:

    // $t9 := 2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:51:33+3
    assume {:print "$at(2,1322,1325)"} true;
    $t9 := 2;
    assume $IsValid'u64'($t9);

    // $t10 := ==($t0, $t9) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:51:30+2
    $t10 := $IsEqual'u64'($t0, $t9);

    // if ($t10) goto L3 else goto L2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:51:14+147
    if ($t10) { goto L3; } else { goto L2; }

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:21+10
    assume {:print "$at(2,1348,1358)"} true;
L3:

    // $t11 := 124700 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:21+10
    assume {:print "$at(2,1348,1358)"} true;
    $t11 := 124700;
    assume $IsValid'u64'($t11);

    // $t12 := 21500 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:33+9
    $t12 := 21500;
    assume $IsValid'u64'($t12);

    // $t13 := [65, 80, 84] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:44+8
    $t13 := MakeVec3(65, 80, 84);
    assume $IsValid'vec'u8''($t13);

    // trace_return[0]($t11) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    assume {:print "$track_return(9,1,0):", $t11} $t11 == $t11;

    // trace_return[1]($t12) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    assume {:print "$track_return(9,1,1):", $t12} $t12 == $t12;

    // trace_return[2]($t13) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    assume {:print "$track_return(9,1,2):", $t13} $t13 == $t13;

    // $t6 := move($t11) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    $t6 := $t11;

    // $t7 := move($t12) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    $t7 := $t12;

    // $t8 := move($t13) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    $t8 := $t13;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    goto L4;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:21+10
    assume {:print "$at(2,1416,1426)"} true;
L2:

    // $t14 := 2750000 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:21+10
    assume {:print "$at(2,1416,1426)"} true;
    $t14 := 2750000;
    assume $IsValid'u64'($t14);

    // $t15 := 1310 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:33+10
    $t15 := 1310;
    assume $IsValid'u64'($t15);

    // $t16 := [87, 69, 84, 72] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:45+9
    $t16 := MakeVec4(87, 69, 84, 72);
    assume $IsValid'vec'u8''($t16);

    // trace_return[0]($t14) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:13+42
    assume {:print "$track_return(9,1,0):", $t14} $t14 == $t14;

    // trace_return[1]($t15) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:13+42
    assume {:print "$track_return(9,1,1):", $t15} $t15 == $t15;

    // trace_return[2]($t16) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:13+42
    assume {:print "$track_return(9,1,2):", $t16} $t16 == $t16;

    // $t6 := move($t14) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:13+42
    $t6 := $t14;

    // $t7 := move($t15) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:13+42
    $t7 := $t15;

    // $t8 := move($t16) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:13+42
    $t8 := $t16;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:55:5+1
    assume {:print "$at(2,1456,1457)"} true;
L4:

    // return ($t6, $t7, $t8) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:55:5+1
    assume {:print "$at(2,1456,1457)"} true;
    $ret0 := $t6;
    $ret1 := $t7;
    $ret2 := $t8;
    return;

}

// fun Liquidity_pool_calculator::get_supply [verification] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:48:5+317
procedure {:timeLimit 40} $42_Liquidity_pool_calculator_get_supply$verify(_$t0: int) returns ($ret0: int, $ret1: int, $ret2: Vec (int))
{
    // declare local variables
    var $t1: int;
    var $t2: bool;
    var $t3: int;
    var $t4: int;
    var $t5: Vec (int);
    var $t6: int;
    var $t7: int;
    var $t8: Vec (int);
    var $t9: int;
    var $t10: bool;
    var $t11: int;
    var $t12: int;
    var $t13: Vec (int);
    var $t14: int;
    var $t15: int;
    var $t16: Vec (int);
    var $t0: int;
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:48:5+1
    assume {:print "$at(2,1140,1141)"} true;
    assume $IsValid'u64'($t0);

    // trace_local[coin_symbol]($t0) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:48:5+1
    assume {:print "$track_local(9,1,0):", $t0} $t0 == $t0;

    // $t1 := 1 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:49:28+4
    assume {:print "$at(2,1227,1231)"} true;
    $t1 := 1;
    assume $IsValid'u64'($t1);

    // $t2 := ==($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:49:25+2
    $t2 := $IsEqual'u64'($t0, $t1);

    // if ($t2) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:49:9+242
    if ($t2) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:21+10
    assume {:print "$at(2,1254,1264)"} true;
L1:

    // $t3 := 3201 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:21+10
    assume {:print "$at(2,1254,1264)"} true;
    $t3 := 3201;
    assume $IsValid'u64'($t3);

    // $t4 := 312 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:33+10
    $t4 := 312;
    assume $IsValid'u64'($t4);

    // $t5 := [78, 50, 68, 32, 82, 101, 119, 97, 114, 100, 115] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:45+9
    $t5 := ConcatVec(ConcatVec(MakeVec4(78, 50, 68, 32), MakeVec4(82, 101, 119, 97)), MakeVec3(114, 100, 115));
    assume $IsValid'vec'u8''($t5);

    // trace_return[0]($t3) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    assume {:print "$track_return(9,1,0):", $t3} $t3 == $t3;

    // trace_return[1]($t4) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    assume {:print "$track_return(9,1,1):", $t4} $t4 == $t4;

    // trace_return[2]($t5) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    assume {:print "$track_return(9,1,2):", $t5} $t5 == $t5;

    // $t6 := move($t3) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    $t6 := $t3;

    // $t7 := move($t4) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    $t7 := $t4;

    // $t8 := move($t5) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    $t8 := $t5;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:50:13+42
    goto L4;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:51:18+11
    assume {:print "$at(2,1307,1318)"} true;
L0:

    // $t9 := 2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:51:33+3
    assume {:print "$at(2,1322,1325)"} true;
    $t9 := 2;
    assume $IsValid'u64'($t9);

    // $t10 := ==($t0, $t9) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:51:30+2
    $t10 := $IsEqual'u64'($t0, $t9);

    // if ($t10) goto L3 else goto L2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:51:14+147
    if ($t10) { goto L3; } else { goto L2; }

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:21+10
    assume {:print "$at(2,1348,1358)"} true;
L3:

    // $t11 := 124700 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:21+10
    assume {:print "$at(2,1348,1358)"} true;
    $t11 := 124700;
    assume $IsValid'u64'($t11);

    // $t12 := 21500 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:33+9
    $t12 := 21500;
    assume $IsValid'u64'($t12);

    // $t13 := [65, 80, 84] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:44+8
    $t13 := MakeVec3(65, 80, 84);
    assume $IsValid'vec'u8''($t13);

    // trace_return[0]($t11) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    assume {:print "$track_return(9,1,0):", $t11} $t11 == $t11;

    // trace_return[1]($t12) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    assume {:print "$track_return(9,1,1):", $t12} $t12 == $t12;

    // trace_return[2]($t13) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    assume {:print "$track_return(9,1,2):", $t13} $t13 == $t13;

    // $t6 := move($t11) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    $t6 := $t11;

    // $t7 := move($t12) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    $t7 := $t12;

    // $t8 := move($t13) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    $t8 := $t13;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:52:13+40
    goto L4;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:21+10
    assume {:print "$at(2,1416,1426)"} true;
L2:

    // $t14 := 2750000 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:21+10
    assume {:print "$at(2,1416,1426)"} true;
    $t14 := 2750000;
    assume $IsValid'u64'($t14);

    // $t15 := 1310 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:33+10
    $t15 := 1310;
    assume $IsValid'u64'($t15);

    // $t16 := [87, 69, 84, 72] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:45+9
    $t16 := MakeVec4(87, 69, 84, 72);
    assume $IsValid'vec'u8''($t16);

    // trace_return[0]($t14) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:13+42
    assume {:print "$track_return(9,1,0):", $t14} $t14 == $t14;

    // trace_return[1]($t15) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:13+42
    assume {:print "$track_return(9,1,1):", $t15} $t15 == $t15;

    // trace_return[2]($t16) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:13+42
    assume {:print "$track_return(9,1,2):", $t16} $t16 == $t16;

    // $t6 := move($t14) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:13+42
    $t6 := $t14;

    // $t7 := move($t15) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:13+42
    $t7 := $t15;

    // $t8 := move($t16) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:54:13+42
    $t8 := $t16;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:55:5+1
    assume {:print "$at(2,1456,1457)"} true;
L4:

    // return ($t6, $t7, $t8) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:55:5+1
    assume {:print "$at(2,1456,1457)"} true;
    $ret0 := $t6;
    $ret1 := $t7;
    $ret2 := $t8;
    return;

}

// fun Liquidity_pool_calculator::test_function [verification] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:82:5+672
procedure {:timeLimit 40} $42_Liquidity_pool_calculator_test_function$verify() returns ()
{
    // declare local variables
    var $t0: $1_string_String;
    var $t1: $1_string_String;
    var $t2: $1_string_String;
    var $t3: $1_string_String;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: Vec (int);
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: Vec (int);
    var $t17: int;
    var $t18: int;
    var $t19: Vec (int);
    var $t20: $1_string_String;
    var $t21: $1_string_String;
    var $t22: Vec (int);
    var $t23: $1_string_String;
    var $t24: int;
    var $t25: int;
    var $t26: Vec (int);
    var $t27: $1_string_String;
    var $t28: int;
    var $t29: int;
    var $t30: int;
    var $temp_0'u64': int;
    var $temp_0'vec'u8'': Vec (int);

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t13 := 2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:83:47+3
    assume {:print "$at(2,2254,2257)"} true;
    $t13 := 2;
    assume $IsValid'u64'($t13);

    // ($t14, $t15, $t16) := Liquidity_pool_calculator::get_supply($t13) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:83:36+15
    call $t14,$t15,$t16 := $42_Liquidity_pool_calculator_get_supply($t13);
    if ($abort_flag) {
        assume {:print "$at(2,2243,2258)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // trace_local[name]($t16) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:83:28+4
    assume {:print "$track_local(9,2,8):", $t16} $t16 == $t16;

    // trace_local[coin2]($t15) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:83:21+5
    assume {:print "$track_local(9,2,6):", $t15} $t15 == $t15;

    // trace_local[coin1]($t14) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:83:14+5
    assume {:print "$track_local(9,2,4):", $t14} $t14 == $t14;

    // $t18 := 2340 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:84:27+4
    assume {:print "$at(2,2287,2291)"} true;
    $t18 := 2340;
    assume $IsValid'u64'($t18);

    // trace_local[swap_amount]($t18) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:84:13+11
    assume {:print "$track_local(9,2,12):", $t18} $t18 == $t18;

    // $t19 := [83, 119, 97, 112, 32, 85, 83, 68, 84, 32, 102, 111, 114, 58] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:85:21+17
    assume {:print "$at(2,2331,2348)"} true;
    $t19 := ConcatVec(ConcatVec(ConcatVec(MakeVec4(83, 119, 97, 112), MakeVec4(32, 85, 83, 68)), MakeVec4(84, 32, 102, 111)), MakeVec2(114, 58));
    assume $IsValid'vec'u8''($t19);

    // $t20 := string::utf8($t19) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:85:16+23
    call $t20 := $1_string_utf8($t19);
    if ($abort_flag) {
        assume {:print "$at(2,2326,2349)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // debug::print<string::String>($t20) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:85:9+31
    call $1_debug_print'$1_string_String'($t20);
    if ($abort_flag) {
        assume {:print "$at(2,2319,2350)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // $t21 := string::utf8($t16) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:86:16+10
    assume {:print "$at(2,2368,2378)"} true;
    call $t21 := $1_string_utf8($t16);
    if ($abort_flag) {
        assume {:print "$at(2,2368,2378)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // debug::print<string::String>($t21) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:86:9+18
    call $1_debug_print'$1_string_String'($t21);
    if ($abort_flag) {
        assume {:print "$at(2,2361,2379)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // $t22 := [84, 111, 107, 101, 110, 32, 80, 114, 105, 99, 101, 32, 66, 101, 102, 111, 114, 101, 32, 83, 119, 97, 112] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:88:21+26
    assume {:print "$at(2,2404,2430)"} true;
    $t22 := ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(84, 111, 107, 101), MakeVec4(110, 32, 80, 114)), MakeVec4(105, 99, 101, 32)), MakeVec4(66, 101, 102, 111)), MakeVec4(114, 101, 32, 83)), MakeVec3(119, 97, 112));
    assume $IsValid'vec'u8''($t22);

    // $t23 := string::utf8($t22) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:88:16+32
    call $t23 := $1_string_utf8($t22);
    if ($abort_flag) {
        assume {:print "$at(2,2399,2431)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // debug::print<string::String>($t23) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:88:9+40
    call $1_debug_print'$1_string_String'($t23);
    if ($abort_flag) {
        assume {:print "$at(2,2392,2432)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // $t24 := Liquidity_pool_calculator::token_price($t14, $t15) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:89:28+25
    assume {:print "$at(2,2462,2487)"} true;
    call $t24 := $42_Liquidity_pool_calculator_token_price($t14, $t15);
    if ($abort_flag) {
        assume {:print "$at(2,2462,2487)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // trace_local[price_before]($t24) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:89:13+12
    assume {:print "$track_local(9,2,10):", $t24} $t24 == $t24;

    // debug::print<u64>($t24) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:90:9+20
    assume {:print "$at(2,2498,2518)"} true;
    call $1_debug_print'u64'($t24);
    if ($abort_flag) {
        assume {:print "$at(2,2498,2518)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // $t25 := Liquidity_pool_calculator::calculate_swap($t14, $t15, $t18) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:92:22+41
    assume {:print "$at(2,2544,2585)"} true;
    call $t25 := $42_Liquidity_pool_calculator_calculate_swap($t14, $t15, $t18);
    if ($abort_flag) {
        assume {:print "$at(2,2544,2585)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // trace_local[result]($t25) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:92:13+6
    assume {:print "$track_local(9,2,11):", $t25} $t25 == $t25;

    // debug::print<u64>($t25) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:93:9+14
    assume {:print "$at(2,2596,2610)"} true;
    call $1_debug_print'u64'($t25);
    if ($abort_flag) {
        assume {:print "$at(2,2596,2610)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // $t26 := [84, 111, 107, 101, 110, 32, 80, 114, 105, 99, 101, 32, 65, 102, 116, 101, 114, 32, 83, 119, 97, 112] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:95:21+25
    assume {:print "$at(2,2635,2660)"} true;
    $t26 := ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(MakeVec4(84, 111, 107, 101), MakeVec4(110, 32, 80, 114)), MakeVec4(105, 99, 101, 32)), MakeVec4(65, 102, 116, 101)), MakeVec4(114, 32, 83, 119)), MakeVec2(97, 112));
    assume $IsValid'vec'u8''($t26);

    // $t27 := string::utf8($t26) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:95:16+31
    call $t27 := $1_string_utf8($t26);
    if ($abort_flag) {
        assume {:print "$at(2,2630,2661)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // debug::print<string::String>($t27) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:95:9+39
    call $1_debug_print'$1_string_String'($t27);
    if ($abort_flag) {
        assume {:print "$at(2,2623,2662)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // $t28 := +($t14, $t18) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:96:33+1
    assume {:print "$at(2,2697,2698)"} true;
    call $t28 := $AddU64($t14, $t18);
    if ($abort_flag) {
        assume {:print "$at(2,2697,2698)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // trace_local[coin1_after]($t28) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:96:13+11
    assume {:print "$track_local(9,2,5):", $t28} $t28 == $t28;

    // $t29 := -($t15, $t25) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:97:33+1
    assume {:print "$at(2,2745,2746)"} true;
    call $t29 := $Sub($t15, $t25);
    if ($abort_flag) {
        assume {:print "$at(2,2745,2746)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // trace_local[coin2_after]($t29) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:97:13+11
    assume {:print "$track_local(9,2,7):", $t29} $t29 == $t29;

    // $t30 := Liquidity_pool_calculator::token_price($t28, $t29) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:98:27+37
    assume {:print "$at(2,2782,2819)"} true;
    call $t30 := $42_Liquidity_pool_calculator_token_price($t28, $t29);
    if ($abort_flag) {
        assume {:print "$at(2,2782,2819)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // trace_local[price_after]($t30) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:98:13+11
    assume {:print "$track_local(9,2,9):", $t30} $t30 == $t30;

    // debug::print<u64>($t30) on_abort goto L2 with $t17 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:99:9+19
    assume {:print "$at(2,2830,2849)"} true;
    call $1_debug_print'u64'($t30);
    if ($abort_flag) {
        assume {:print "$at(2,2830,2849)"} true;
        $t17 := $abort_code;
        assume {:print "$track_abort(9,2):", $t17} $t17 == $t17;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:100:5+1
    assume {:print "$at(2,2856,2857)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:100:5+1
    assume {:print "$at(2,2856,2857)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:100:5+1
L2:

    // abort($t17) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:100:5+1
    assume {:print "$at(2,2856,2857)"} true;
    $abort_code := $t17;
    $abort_flag := true;
    return;

}

// fun Liquidity_pool_calculator::token_price [baseline] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:57:5+167
procedure {:inline 1} $42_Liquidity_pool_calculator_token_price(_$t0: int, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[coin1]($t0) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:57:5+1
    assume {:print "$at(2,1465,1466)"} true;
    assume {:print "$track_local(9,3,0):", $t0} $t0 == $t0;

    // trace_local[coin2]($t1) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:57:5+1
    assume {:print "$track_local(9,3,1):", $t1} $t1 == $t1;

    // $t2 := 0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:25+1
    assume {:print "$at(2,1537,1538)"} true;
    $t2 := 0;
    assume $IsValid'u64'($t2);

    // $t3 := >($t0, $t2) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:23+1
    call $t3 := $Gt($t0, $t2);

    // if ($t3) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:9+31
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:9+31
L1:

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:9+31
    assume {:print "$at(2,1521,1552)"} true;
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:28+11
L0:

    // $t4 := 0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:28+11
    assume {:print "$at(2,1540,1551)"} true;
    $t4 := 0;
    assume $IsValid'u64'($t4);

    // trace_abort($t4) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:9+31
    assume {:print "$at(2,1521,1552)"} true;
    assume {:print "$track_abort(9,3):", $t4} $t4 == $t4;

    // $t5 := move($t4) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:9+31
    $t5 := $t4;

    // goto L7 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:9+31
    goto L7;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:17+5
    assume {:print "$at(2,1571,1576)"} true;
L2:

    // $t6 := 0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:25+1
    assume {:print "$at(2,1579,1580)"} true;
    $t6 := 0;
    assume $IsValid'u64'($t6);

    // $t7 := >($t1, $t6) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:23+1
    call $t7 := $Gt($t1, $t6);

    // if ($t7) goto L4 else goto L3 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:9+31
    if ($t7) { goto L4; } else { goto L3; }

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:9+31
L4:

    // goto L5 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:9+31
    assume {:print "$at(2,1563,1594)"} true;
    goto L5;

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:28+11
L3:

    // $t8 := 0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:28+11
    assume {:print "$at(2,1582,1593)"} true;
    $t8 := 0;
    assume $IsValid'u64'($t8);

    // trace_abort($t8) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:9+31
    assume {:print "$at(2,1563,1594)"} true;
    assume {:print "$track_abort(9,3):", $t8} $t8 == $t8;

    // $t5 := move($t8) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:9+31
    $t5 := $t8;

    // goto L7 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:9+31
    goto L7;

    // label L5 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:60:16+5
    assume {:print "$at(2,1612,1617)"} true;
L5:

    // $t9 := /($t0, $t1) on_abort goto L7 with $t5 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:60:22+1
    assume {:print "$at(2,1618,1619)"} true;
    call $t9 := $Div($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,1618,1619)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(9,3):", $t5} $t5 == $t5;
        goto L7;
    }

    // trace_return[0]($t9) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:60:9+20
    assume {:print "$track_return(9,3,0):", $t9} $t9 == $t9;

    // label L6 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:61:5+1
    assume {:print "$at(2,1631,1632)"} true;
L6:

    // return $t9 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:61:5+1
    assume {:print "$at(2,1631,1632)"} true;
    $ret0 := $t9;
    return;

    // label L7 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:61:5+1
L7:

    // abort($t5) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:61:5+1
    assume {:print "$at(2,1631,1632)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun Liquidity_pool_calculator::token_price [verification] at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:57:5+167
procedure {:timeLimit 40} $42_Liquidity_pool_calculator_token_price$verify(_$t0: int, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:57:5+1
    assume {:print "$at(2,1465,1466)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:57:5+1
    assume $IsValid'u64'($t1);

    // trace_local[coin1]($t0) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:57:5+1
    assume {:print "$track_local(9,3,0):", $t0} $t0 == $t0;

    // trace_local[coin2]($t1) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:57:5+1
    assume {:print "$track_local(9,3,1):", $t1} $t1 == $t1;

    // $t2 := 0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:25+1
    assume {:print "$at(2,1537,1538)"} true;
    $t2 := 0;
    assume $IsValid'u64'($t2);

    // $t3 := >($t0, $t2) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:23+1
    call $t3 := $Gt($t0, $t2);

    // if ($t3) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:9+31
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:9+31
L1:

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:9+31
    assume {:print "$at(2,1521,1552)"} true;
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:28+11
L0:

    // $t4 := 0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:28+11
    assume {:print "$at(2,1540,1551)"} true;
    $t4 := 0;
    assume $IsValid'u64'($t4);

    // trace_abort($t4) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:9+31
    assume {:print "$at(2,1521,1552)"} true;
    assume {:print "$track_abort(9,3):", $t4} $t4 == $t4;

    // $t5 := move($t4) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:9+31
    $t5 := $t4;

    // goto L7 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:58:9+31
    goto L7;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:17+5
    assume {:print "$at(2,1571,1576)"} true;
L2:

    // $t6 := 0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:25+1
    assume {:print "$at(2,1579,1580)"} true;
    $t6 := 0;
    assume $IsValid'u64'($t6);

    // $t7 := >($t1, $t6) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:23+1
    call $t7 := $Gt($t1, $t6);

    // if ($t7) goto L4 else goto L3 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:9+31
    if ($t7) { goto L4; } else { goto L3; }

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:9+31
L4:

    // goto L5 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:9+31
    assume {:print "$at(2,1563,1594)"} true;
    goto L5;

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:28+11
L3:

    // $t8 := 0 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:28+11
    assume {:print "$at(2,1582,1593)"} true;
    $t8 := 0;
    assume $IsValid'u64'($t8);

    // trace_abort($t8) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:9+31
    assume {:print "$at(2,1563,1594)"} true;
    assume {:print "$track_abort(9,3):", $t8} $t8 == $t8;

    // $t5 := move($t8) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:9+31
    $t5 := $t8;

    // goto L7 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:59:9+31
    goto L7;

    // label L5 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:60:16+5
    assume {:print "$at(2,1612,1617)"} true;
L5:

    // $t9 := /($t0, $t1) on_abort goto L7 with $t5 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:60:22+1
    assume {:print "$at(2,1618,1619)"} true;
    call $t9 := $Div($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,1618,1619)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(9,3):", $t5} $t5 == $t5;
        goto L7;
    }

    // trace_return[0]($t9) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:60:9+20
    assume {:print "$track_return(9,3,0):", $t9} $t9 == $t9;

    // label L6 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:61:5+1
    assume {:print "$at(2,1631,1632)"} true;
L6:

    // return $t9 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:61:5+1
    assume {:print "$at(2,1631,1632)"} true;
    $ret0 := $t9;
    return;

    // label L7 at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:61:5+1
L7:

    // abort($t5) at /mnt/c/Users/DELL/move-tut/sources/Liquidity_pool_calculator.move:61:5+1
    assume {:print "$at(2,1631,1632)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun Sample4::test_function [verification] at /mnt/c/Users/DELL/move-tut/sources/simple4.move:23:5+103
procedure {:timeLimit 40} $42_Sample4_test_function$verify() returns ()
{
    // declare local variables
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $temp_0'u64': int;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t1 := 10 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:24:38+2
    assume {:print "$at(11,529,531)"} true;
    $t1 := 10;
    assume $IsValid'u64'($t1);

    // $t2 := Sample4::simple_for_loop($t1) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:24:22+19
    call $t2 := $42_Sample4_simple_for_loop($t1);
    if ($abort_flag) {
        assume {:print "$at(11,513,532)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(10,2):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_local[result]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:24:13+6
    assume {:print "$track_local(10,2,0):", $t2} $t2 == $t2;

    // debug::print<u64>($t2) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:25:9+21
    assume {:print "$at(11,543,564)"} true;
    call $1_debug_print'u64'($t2);
    if ($abort_flag) {
        assume {:print "$at(11,543,564)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(10,2):", $t3} $t3 == $t3;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:26:5+1
    assume {:print "$at(11,571,572)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple4.move:26:5+1
    assume {:print "$at(11,571,572)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:26:5+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:26:5+1
    assume {:print "$at(11,571,572)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun Sample4::simple_for_loop [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple4.move:4:5+170
procedure {:inline 1} $42_Sample4_simple_for_loop(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: int;
    var $t10: bool;
    var $t11: bool;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t0: int;
    var $temp_0'bool': bool;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[count]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:4:5+1
    assume {:print "$at(11,55,56)"} true;
    assume {:print "$track_local(10,0,0):", $t0} $t0 == $t0;

    // $t5 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:5:22+1
    assume {:print "$at(11,116,117)"} true;
    $t5 := 0;
    assume $IsValid'u64'($t5);

    // trace_local[result]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:5:13+6
    assume {:print "$track_local(10,0,4):", $t5} $t5 == $t5;

    // $t6 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:19+1
    assume {:print "$at(11,138,139)"} true;
    $t6 := 0;
    assume $IsValid'u64'($t6);

    // trace_local[i]($t6) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,3):", $t6} $t6 == $t6;

    // $t7 := false at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    $t7 := false;
    assume $IsValid'bool'($t7);

    // trace_local[__update_iter_flag]($t7) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,1):", $t7} $t7 == $t7;

    // trace_local[__upper_bound_value]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,2):", $t0} $t0 == $t0;

    // label L5 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
L5:

    // $t1 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$at(11,128,193)"} true;
    havoc $t1;

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'bool'($t1);

    // $t3 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t3;

    // assume WellFormed($t3) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'u64'($t3);

    // $t4 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t4;

    // assume WellFormed($t4) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'u64'($t4);

    // $t8 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t8;

    // assume WellFormed($t8) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'u64'($t8);

    // $t9 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t9;

    // assume WellFormed($t9) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'u64'($t9);

    // $t10 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t10;

    // assume WellFormed($t10) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'bool'($t10);

    // $t11 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t11;

    // assume WellFormed($t11) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'bool'($t11);

    // $t12 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t12;

    // assume WellFormed($t12) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'u64'($t12);

    // trace_local[__update_iter_flag]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$info(): enter loop, variable(s) __update_iter_flag, i, result havocked and reassigned"} true;
    assume {:print "$track_local(10,0,1):", $t1} $t1 == $t1;

    // trace_local[i]($t3) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,3):", $t3} $t3 == $t3;

    // trace_local[result]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,4):", $t4} $t4 == $t4;

    // assume Not(AbortFlag()) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume !$abort_flag;

    // if ($t1) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    if ($t1) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
L1:

    // $t8 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$at(11,128,193)"} true;
    $t8 := 1;
    assume $IsValid'u64'($t8);

    // $t9 := +($t3, $t8) on_abort goto L8 with $t13 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    call $t9 := $AddU64($t3, $t8);
    if ($abort_flag) {
        assume {:print "$at(11,128,193)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(10,0):", $t13} $t13 == $t13;
        goto L8;
    }

    // $t3 := $t9 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    $t3 := $t9;

    // trace_local[i]($t9) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,3):", $t9} $t9 == $t9;

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
L0:

    // $t10 := true at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$at(11,128,193)"} true;
    $t10 := true;
    assume $IsValid'bool'($t10);

    // trace_local[__update_iter_flag]($t10) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,1):", $t10} $t10 == $t10;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
L2:

    // $t11 := <($t3, $t0) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:14+1
    assume {:print "$at(11,133,134)"} true;
    call $t11 := $Lt($t3, $t0);

    // if ($t11) goto L4 else goto L3 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    if ($t11) { goto L4; } else { goto L3; }

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:7:22+6
    assume {:print "$at(11,171,177)"} true;
L4:

    // $t12 := +($t4, $t3) on_abort goto L8 with $t13 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:7:29+1
    assume {:print "$at(11,178,179)"} true;
    call $t12 := $AddU64($t4, $t3);
    if ($abort_flag) {
        assume {:print "$at(11,178,179)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(10,0):", $t13} $t13 == $t13;
        goto L8;
    }

    // trace_local[result]($t12) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:7:13+6
    assume {:print "$track_local(10,0,4):", $t12} $t12 == $t12;

    // goto L6 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$at(11,128,193)"} true;
    goto L6;

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:9:16+6
    assume {:print "$at(11,211,217)"} true;
L3:

    // trace_return[0]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:9:9+13
    assume {:print "$at(11,204,217)"} true;
    assume {:print "$track_return(10,0,0):", $t4} $t4 == $t4;

    // $t14 := move($t4) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:9:9+13
    $t14 := $t4;

    // goto L7 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:9:9+13
    goto L7;

    // label L6 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:9:16+6
    // Loop invariant checking block for the loop started with header: L5
L6:

    // stop() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:9:16+6
    assume {:print "$at(11,211,217)"} true;
    assume false;
    return;

    // label L7 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:10:5+1
    assume {:print "$at(11,224,225)"} true;
L7:

    // return $t14 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:10:5+1
    assume {:print "$at(11,224,225)"} true;
    $ret0 := $t14;
    return;

    // label L8 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:10:5+1
L8:

    // abort($t13) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:10:5+1
    assume {:print "$at(11,224,225)"} true;
    $abort_code := $t13;
    $abort_flag := true;
    return;

}

// fun Sample4::simple_for_loop [verification] at /mnt/c/Users/DELL/move-tut/sources/simple4.move:4:5+170
procedure {:timeLimit 40} $42_Sample4_simple_for_loop$verify(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: int;
    var $t10: bool;
    var $t11: bool;
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t0: int;
    var $temp_0'bool': bool;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:4:5+1
    assume {:print "$at(11,55,56)"} true;
    assume $IsValid'u64'($t0);

    // trace_local[count]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:4:5+1
    assume {:print "$track_local(10,0,0):", $t0} $t0 == $t0;

    // $t5 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:5:22+1
    assume {:print "$at(11,116,117)"} true;
    $t5 := 0;
    assume $IsValid'u64'($t5);

    // trace_local[result]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:5:13+6
    assume {:print "$track_local(10,0,4):", $t5} $t5 == $t5;

    // $t6 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:19+1
    assume {:print "$at(11,138,139)"} true;
    $t6 := 0;
    assume $IsValid'u64'($t6);

    // trace_local[i]($t6) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,3):", $t6} $t6 == $t6;

    // $t7 := false at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    $t7 := false;
    assume $IsValid'bool'($t7);

    // trace_local[__update_iter_flag]($t7) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,1):", $t7} $t7 == $t7;

    // trace_local[__upper_bound_value]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,2):", $t0} $t0 == $t0;

    // label L5 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
L5:

    // $t1 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$at(11,128,193)"} true;
    havoc $t1;

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'bool'($t1);

    // $t3 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t3;

    // assume WellFormed($t3) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'u64'($t3);

    // $t4 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t4;

    // assume WellFormed($t4) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'u64'($t4);

    // $t8 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t8;

    // assume WellFormed($t8) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'u64'($t8);

    // $t9 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t9;

    // assume WellFormed($t9) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'u64'($t9);

    // $t10 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t10;

    // assume WellFormed($t10) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'bool'($t10);

    // $t11 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t11;

    // assume WellFormed($t11) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'bool'($t11);

    // $t12 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    havoc $t12;

    // assume WellFormed($t12) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume $IsValid'u64'($t12);

    // trace_local[__update_iter_flag]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$info(): enter loop, variable(s) __update_iter_flag, i, result havocked and reassigned"} true;
    assume {:print "$track_local(10,0,1):", $t1} $t1 == $t1;

    // trace_local[i]($t3) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,3):", $t3} $t3 == $t3;

    // trace_local[result]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,4):", $t4} $t4 == $t4;

    // assume Not(AbortFlag()) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume !$abort_flag;

    // if ($t1) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    if ($t1) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
L1:

    // $t8 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$at(11,128,193)"} true;
    $t8 := 1;
    assume $IsValid'u64'($t8);

    // $t9 := +($t3, $t8) on_abort goto L8 with $t13 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    call $t9 := $AddU64($t3, $t8);
    if ($abort_flag) {
        assume {:print "$at(11,128,193)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(10,0):", $t13} $t13 == $t13;
        goto L8;
    }

    // $t3 := $t9 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    $t3 := $t9;

    // trace_local[i]($t9) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,3):", $t9} $t9 == $t9;

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
L0:

    // $t10 := true at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$at(11,128,193)"} true;
    $t10 := true;
    assume $IsValid'bool'($t10);

    // trace_local[__update_iter_flag]($t10) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$track_local(10,0,1):", $t10} $t10 == $t10;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
L2:

    // $t11 := <($t3, $t0) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:14+1
    assume {:print "$at(11,133,134)"} true;
    call $t11 := $Lt($t3, $t0);

    // if ($t11) goto L4 else goto L3 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    if ($t11) { goto L4; } else { goto L3; }

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:7:22+6
    assume {:print "$at(11,171,177)"} true;
L4:

    // $t12 := +($t4, $t3) on_abort goto L8 with $t13 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:7:29+1
    assume {:print "$at(11,178,179)"} true;
    call $t12 := $AddU64($t4, $t3);
    if ($abort_flag) {
        assume {:print "$at(11,178,179)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(10,0):", $t13} $t13 == $t13;
        goto L8;
    }

    // trace_local[result]($t12) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:7:13+6
    assume {:print "$track_local(10,0,4):", $t12} $t12 == $t12;

    // goto L6 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:6:9+65
    assume {:print "$at(11,128,193)"} true;
    goto L6;

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:9:16+6
    assume {:print "$at(11,211,217)"} true;
L3:

    // trace_return[0]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:9:9+13
    assume {:print "$at(11,204,217)"} true;
    assume {:print "$track_return(10,0,0):", $t4} $t4 == $t4;

    // $t14 := move($t4) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:9:9+13
    $t14 := $t4;

    // goto L7 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:9:9+13
    goto L7;

    // label L6 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:9:16+6
    // Loop invariant checking block for the loop started with header: L5
L6:

    // stop() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:9:16+6
    assume {:print "$at(11,211,217)"} true;
    assume false;
    return;

    // label L7 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:10:5+1
    assume {:print "$at(11,224,225)"} true;
L7:

    // return $t14 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:10:5+1
    assume {:print "$at(11,224,225)"} true;
    $ret0 := $t14;
    return;

    // label L8 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:10:5+1
L8:

    // abort($t13) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:10:5+1
    assume {:print "$at(11,224,225)"} true;
    $abort_code := $t13;
    $abort_flag := true;
    return;

}

// fun Sample4::simple_while_loop [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple4.move:12:5+208
procedure {:inline 1} $42_Sample4_simple_while_loop(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: bool;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[count]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:12:5+1
    assume {:print "$at(11,237,238)"} true;
    assume {:print "$track_local(10,1,0):", $t0} $t0 == $t0;

    // $t3 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:13:22+1
    assume {:print "$at(11,300,301)"} true;
    $t3 := 0;
    assume $IsValid'u64'($t3);

    // trace_local[result]($t3) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:13:13+6
    assume {:print "$track_local(10,1,2):", $t3} $t3 == $t3;

    // $t4 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:14:17+1
    assume {:print "$at(11,320,321)"} true;
    $t4 := 1;
    assume $IsValid'u64'($t4);

    // trace_local[i]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:14:13+1
    assume {:print "$track_local(10,1,1):", $t4} $t4 == $t4;

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume {:print "$at(11,339,340)"} true;
L3:

    // $t1 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume {:print "$at(11,339,340)"} true;
    havoc $t1;

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'u64'($t1);

    // $t2 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    havoc $t2;

    // assume WellFormed($t2) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'u64'($t2);

    // $t5 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    havoc $t5;

    // assume WellFormed($t5) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'bool'($t5);

    // $t6 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    havoc $t6;

    // assume WellFormed($t6) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'u64'($t6);

    // $t7 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    havoc $t7;

    // assume WellFormed($t7) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'u64'($t7);

    // $t8 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    havoc $t8;

    // assume WellFormed($t8) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'u64'($t8);

    // $t9 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    havoc $t9;

    // assume WellFormed($t9) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'u64'($t9);

    // trace_local[i]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume {:print "$info(): enter loop, variable(s) i, result havocked and reassigned"} true;
    assume {:print "$track_local(10,1,1):", $t1} $t1 == $t1;

    // trace_local[result]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume {:print "$track_local(10,1,2):", $t2} $t2 == $t2;

    // assume Not(AbortFlag()) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume !$abort_flag;

    // $t5 := <=($t1, $t0) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:18+2
    call $t5 := $Le($t1, $t0);

    // if ($t5) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:9+89
    if ($t5) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:9+89
L1:

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:16:22+6
    assume {:print "$at(11,375,381)"} true;
L2:

    // $t6 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:16:31+1
    assume {:print "$at(11,384,385)"} true;
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := +($t2, $t6) on_abort goto L6 with $t10 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:16:29+1
    call $t7 := $AddU64($t2, $t6);
    if ($abort_flag) {
        assume {:print "$at(11,382,383)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(10,1):", $t10} $t10 == $t10;
        goto L6;
    }

    // trace_local[result]($t7) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:16:13+6
    assume {:print "$track_local(10,1,2):", $t7} $t7 == $t7;

    // $t8 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:17:21+1
    assume {:print "$at(11,408,409)"} true;
    $t8 := 1;
    assume $IsValid'u64'($t8);

    // $t9 := +($t1, $t8) on_abort goto L6 with $t10 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:17:19+1
    call $t9 := $AddU64($t1, $t8);
    if ($abort_flag) {
        assume {:print "$at(11,406,407)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(10,1):", $t10} $t10 == $t10;
        goto L6;
    }

    // trace_local[i]($t9) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:17:13+1
    assume {:print "$track_local(10,1,1):", $t9} $t9 == $t9;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:17:22+1
    goto L4;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:19:9+6
    assume {:print "$at(11,432,438)"} true;
L0:

    // trace_return[0]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:19:9+6
    assume {:print "$at(11,432,438)"} true;
    assume {:print "$track_return(10,1,0):", $t2} $t2 == $t2;

    // $t11 := move($t2) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:19:9+6
    $t11 := $t2;

    // goto L5 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:19:9+6
    goto L5;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:19:9+6
    // Loop invariant checking block for the loop started with header: L3
L4:

    // stop() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:19:9+6
    assume {:print "$at(11,432,438)"} true;
    assume false;
    return;

    // label L5 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:20:5+1
    assume {:print "$at(11,444,445)"} true;
L5:

    // return $t11 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:20:5+1
    assume {:print "$at(11,444,445)"} true;
    $ret0 := $t11;
    return;

    // label L6 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:20:5+1
L6:

    // abort($t10) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:20:5+1
    assume {:print "$at(11,444,445)"} true;
    $abort_code := $t10;
    $abort_flag := true;
    return;

}

// fun Sample4::simple_while_loop [verification] at /mnt/c/Users/DELL/move-tut/sources/simple4.move:12:5+208
procedure {:timeLimit 40} $42_Sample4_simple_while_loop$verify(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: bool;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:12:5+1
    assume {:print "$at(11,237,238)"} true;
    assume $IsValid'u64'($t0);

    // trace_local[count]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:12:5+1
    assume {:print "$track_local(10,1,0):", $t0} $t0 == $t0;

    // $t3 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:13:22+1
    assume {:print "$at(11,300,301)"} true;
    $t3 := 0;
    assume $IsValid'u64'($t3);

    // trace_local[result]($t3) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:13:13+6
    assume {:print "$track_local(10,1,2):", $t3} $t3 == $t3;

    // $t4 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:14:17+1
    assume {:print "$at(11,320,321)"} true;
    $t4 := 1;
    assume $IsValid'u64'($t4);

    // trace_local[i]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:14:13+1
    assume {:print "$track_local(10,1,1):", $t4} $t4 == $t4;

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume {:print "$at(11,339,340)"} true;
L3:

    // $t1 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume {:print "$at(11,339,340)"} true;
    havoc $t1;

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'u64'($t1);

    // $t2 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    havoc $t2;

    // assume WellFormed($t2) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'u64'($t2);

    // $t5 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    havoc $t5;

    // assume WellFormed($t5) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'bool'($t5);

    // $t6 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    havoc $t6;

    // assume WellFormed($t6) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'u64'($t6);

    // $t7 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    havoc $t7;

    // assume WellFormed($t7) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'u64'($t7);

    // $t8 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    havoc $t8;

    // assume WellFormed($t8) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'u64'($t8);

    // $t9 := havoc[val]() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    havoc $t9;

    // assume WellFormed($t9) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume $IsValid'u64'($t9);

    // trace_local[i]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume {:print "$info(): enter loop, variable(s) i, result havocked and reassigned"} true;
    assume {:print "$track_local(10,1,1):", $t1} $t1 == $t1;

    // trace_local[result]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume {:print "$track_local(10,1,2):", $t2} $t2 == $t2;

    // assume Not(AbortFlag()) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:16+1
    assume !$abort_flag;

    // $t5 := <=($t1, $t0) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:18+2
    call $t5 := $Le($t1, $t0);

    // if ($t5) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:9+89
    if ($t5) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:15:9+89
L1:

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:16:22+6
    assume {:print "$at(11,375,381)"} true;
L2:

    // $t6 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:16:31+1
    assume {:print "$at(11,384,385)"} true;
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := +($t2, $t6) on_abort goto L6 with $t10 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:16:29+1
    call $t7 := $AddU64($t2, $t6);
    if ($abort_flag) {
        assume {:print "$at(11,382,383)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(10,1):", $t10} $t10 == $t10;
        goto L6;
    }

    // trace_local[result]($t7) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:16:13+6
    assume {:print "$track_local(10,1,2):", $t7} $t7 == $t7;

    // $t8 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:17:21+1
    assume {:print "$at(11,408,409)"} true;
    $t8 := 1;
    assume $IsValid'u64'($t8);

    // $t9 := +($t1, $t8) on_abort goto L6 with $t10 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:17:19+1
    call $t9 := $AddU64($t1, $t8);
    if ($abort_flag) {
        assume {:print "$at(11,406,407)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(10,1):", $t10} $t10 == $t10;
        goto L6;
    }

    // trace_local[i]($t9) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:17:13+1
    assume {:print "$track_local(10,1,1):", $t9} $t9 == $t9;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:17:22+1
    goto L4;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:19:9+6
    assume {:print "$at(11,432,438)"} true;
L0:

    // trace_return[0]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:19:9+6
    assume {:print "$at(11,432,438)"} true;
    assume {:print "$track_return(10,1,0):", $t2} $t2 == $t2;

    // $t11 := move($t2) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:19:9+6
    $t11 := $t2;

    // goto L5 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:19:9+6
    goto L5;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:19:9+6
    // Loop invariant checking block for the loop started with header: L3
L4:

    // stop() at /mnt/c/Users/DELL/move-tut/sources/simple4.move:19:9+6
    assume {:print "$at(11,432,438)"} true;
    assume false;
    return;

    // label L5 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:20:5+1
    assume {:print "$at(11,444,445)"} true;
L5:

    // return $t11 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:20:5+1
    assume {:print "$at(11,444,445)"} true;
    $ret0 := $t11;
    return;

    // label L6 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:20:5+1
L6:

    // abort($t10) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:20:5+1
    assume {:print "$at(11,444,445)"} true;
    $abort_code := $t10;
    $abort_flag := true;
    return;

}

// fun Sample4::test_while_function [verification] at /mnt/c/Users/DELL/move-tut/sources/simple4.move:29:5+111
procedure {:timeLimit 40} $42_Sample4_test_while_function$verify() returns ()
{
    // declare local variables
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $temp_0'u64': int;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t1 := 10 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:30:40+2
    assume {:print "$at(11,664,666)"} true;
    $t1 := 10;
    assume $IsValid'u64'($t1);

    // $t2 := Sample4::simple_while_loop($t1) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:30:22+21
    call $t2 := $42_Sample4_simple_while_loop($t1);
    if ($abort_flag) {
        assume {:print "$at(11,646,667)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(10,3):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_local[result]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:30:13+6
    assume {:print "$track_local(10,3,0):", $t2} $t2 == $t2;

    // debug::print<u64>($t2) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:31:9+21
    assume {:print "$at(11,678,699)"} true;
    call $1_debug_print'u64'($t2);
    if ($abort_flag) {
        assume {:print "$at(11,678,699)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(10,3):", $t3} $t3 == $t3;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:32:5+1
    assume {:print "$at(11,706,707)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple4.move:32:5+1
    assume {:print "$at(11,706,707)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple4.move:32:5+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple4.move:32:5+1
    assume {:print "$at(11,706,707)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun Simple1::test_function [verification] at /mnt/c/Users/DELL/move-tut/sources/simple1.move:19:4+88
procedure {:timeLimit 40} $42_Simple1_test_function$verify() returns ()
{
    // declare local variables
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $temp_0'u64': int;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t1 := Simple1::set_val() on_abort goto L2 with $t2 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:20:20+9
    assume {:print "$at(3,347,356)"} true;
    call $t1 := $42_Simple1_set_val();
    if ($abort_flag) {
        assume {:print "$at(3,347,356)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(11,1):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_local[id_value]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple1.move:20:9+8
    assume {:print "$track_local(11,1,0):", $t1} $t1 == $t1;

    // debug::print<u64>($t1) on_abort goto L2 with $t2 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:21:5+23
    assume {:print "$at(3,363,386)"} true;
    call $1_debug_print'u64'($t1);
    if ($abort_flag) {
        assume {:print "$at(3,363,386)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(11,1):", $t2} $t2 == $t2;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:22:4+1
    assume {:print "$at(3,392,393)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple1.move:22:4+1
    assume {:print "$at(3,392,393)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:22:4+1
L2:

    // abort($t2) at /mnt/c/Users/DELL/move-tut/sources/simple1.move:22:4+1
    assume {:print "$at(3,392,393)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun Simple1::set_val [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple1.move:9:4+160
procedure {:inline 1} $42_Simple1_set_val() returns ($ret0: int)
{
    // declare local variables
    var $t0: int;
    var $t1: $1_string_String;
    var $t2: int;
    var $t3: Vec (int);
    var $t4: $1_string_String;
    var $t5: int;
    var $t6: int;
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'u64': int;
    var $temp_0'u8': int;

    // bytecode translation starts here
    // $t2 := 100 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:10:15+6
    assume {:print "$at(3,160,166)"} true;
    $t2 := 100;
    assume $IsValid'u8'($t2);

    // trace_local[num]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple1.move:10:9+3
    assume {:print "$track_local(11,0,0):", $t2} $t2 == $t2;

    // $t3 := [72, 101, 108, 108, 111, 32, 109, 111, 118, 101] at /mnt/c/Users/DELL/move-tut/sources/simple1.move:11:32+13
    assume {:print "$at(3,200,213)"} true;
    $t3 := ConcatVec(ConcatVec(MakeVec4(72, 101, 108, 108), MakeVec4(111, 32, 109, 111)), MakeVec2(118, 101));
    assume $IsValid'vec'u8''($t3);

    // $t4 := string::utf8($t3) on_abort goto L2 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:11:27+19
    call $t4 := $1_string_utf8($t3);
    if ($abort_flag) {
        assume {:print "$at(3,195,214)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(11,0):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_local[string]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple1.move:11:9+6
    assume {:print "$track_local(11,0,1):", $t4} $t4 == $t4;

    // debug::print<u8>($t2) on_abort goto L2 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:13:5+18
    assume {:print "$at(3,223,241)"} true;
    call $1_debug_print'u8'($t2);
    if ($abort_flag) {
        assume {:print "$at(3,223,241)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(11,0):", $t5} $t5 == $t5;
        goto L2;
    }

    // debug::print<string::String>($t4) on_abort goto L2 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:14:5+21
    assume {:print "$at(3,248,269)"} true;
    call $1_debug_print'$1_string_String'($t4);
    if ($abort_flag) {
        assume {:print "$at(3,248,269)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(11,0):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t6 := 100 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:15:5+2
    assume {:print "$at(3,276,278)"} true;
    $t6 := 100;
    assume $IsValid'u64'($t6);

    // trace_return[0]($t6) at /mnt/c/Users/DELL/move-tut/sources/simple1.move:15:5+2
    assume {:print "$track_return(11,0,0):", $t6} $t6 == $t6;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:16:4+1
    assume {:print "$at(3,283,284)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:16:4+1
    assume {:print "$at(3,283,284)"} true;
    $ret0 := $t6;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:16:4+1
L2:

    // abort($t5) at /mnt/c/Users/DELL/move-tut/sources/simple1.move:16:4+1
    assume {:print "$at(3,283,284)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun Simple1::set_val [verification] at /mnt/c/Users/DELL/move-tut/sources/simple1.move:9:4+160
procedure {:timeLimit 40} $42_Simple1_set_val$verify() returns ($ret0: int)
{
    // declare local variables
    var $t0: int;
    var $t1: $1_string_String;
    var $t2: int;
    var $t3: Vec (int);
    var $t4: $1_string_String;
    var $t5: int;
    var $t6: int;
    var $temp_0'$1_string_String': $1_string_String;
    var $temp_0'u64': int;
    var $temp_0'u8': int;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t2 := 100 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:10:15+6
    assume {:print "$at(3,160,166)"} true;
    $t2 := 100;
    assume $IsValid'u8'($t2);

    // trace_local[num]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple1.move:10:9+3
    assume {:print "$track_local(11,0,0):", $t2} $t2 == $t2;

    // $t3 := [72, 101, 108, 108, 111, 32, 109, 111, 118, 101] at /mnt/c/Users/DELL/move-tut/sources/simple1.move:11:32+13
    assume {:print "$at(3,200,213)"} true;
    $t3 := ConcatVec(ConcatVec(MakeVec4(72, 101, 108, 108), MakeVec4(111, 32, 109, 111)), MakeVec2(118, 101));
    assume $IsValid'vec'u8''($t3);

    // $t4 := string::utf8($t3) on_abort goto L2 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:11:27+19
    call $t4 := $1_string_utf8($t3);
    if ($abort_flag) {
        assume {:print "$at(3,195,214)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(11,0):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_local[string]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple1.move:11:9+6
    assume {:print "$track_local(11,0,1):", $t4} $t4 == $t4;

    // debug::print<u8>($t2) on_abort goto L2 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:13:5+18
    assume {:print "$at(3,223,241)"} true;
    call $1_debug_print'u8'($t2);
    if ($abort_flag) {
        assume {:print "$at(3,223,241)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(11,0):", $t5} $t5 == $t5;
        goto L2;
    }

    // debug::print<string::String>($t4) on_abort goto L2 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:14:5+21
    assume {:print "$at(3,248,269)"} true;
    call $1_debug_print'$1_string_String'($t4);
    if ($abort_flag) {
        assume {:print "$at(3,248,269)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(11,0):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t6 := 100 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:15:5+2
    assume {:print "$at(3,276,278)"} true;
    $t6 := 100;
    assume $IsValid'u64'($t6);

    // trace_return[0]($t6) at /mnt/c/Users/DELL/move-tut/sources/simple1.move:15:5+2
    assume {:print "$track_return(11,0,0):", $t6} $t6 == $t6;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:16:4+1
    assume {:print "$at(3,283,284)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:16:4+1
    assume {:print "$at(3,283,284)"} true;
    $ret0 := $t6;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple1.move:16:4+1
L2:

    // abort($t5) at /mnt/c/Users/DELL/move-tut/sources/simple1.move:16:4+1
    assume {:print "$at(3,283,284)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun Simple7::bitshift_left [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple7.move:57:7+69
procedure {:inline 1} $42_Simple7_bitshift_left(_$t0: int, _$t1: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    var $temp_0'u8': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:57:7+1
    assume {:print "$at(14,1112,1113)"} true;
    assume {:print "$track_local(12,0,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:57:7+1
    assume {:print "$track_local(12,0,1):", $t1} $t1 == $t1;

    // $t2 := <<($t0, $t1) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:58:18+2
    assume {:print "$at(14,1170,1172)"} true;
    call $t2 := $ShlU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(14,1170,1172)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(12,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:58:9+13
    assume {:print "$track_return(12,0,0):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:59:5+1
    assume {:print "$at(14,1180,1181)"} true;
L1:

    // return $t2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:59:5+1
    assume {:print "$at(14,1180,1181)"} true;
    $ret0 := $t2;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:59:5+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:59:5+1
    assume {:print "$at(14,1180,1181)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun Simple7::bitshift_left [verification] at /mnt/c/Users/DELL/move-tut/sources/simple7.move:57:7+69
procedure {:timeLimit 40} $42_Simple7_bitshift_left$verify(_$t0: int, _$t1: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    var $temp_0'u8': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:57:7+1
    assume {:print "$at(14,1112,1113)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:57:7+1
    assume $IsValid'u8'($t1);

    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:57:7+1
    assume {:print "$track_local(12,0,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:57:7+1
    assume {:print "$track_local(12,0,1):", $t1} $t1 == $t1;

    // $t2 := <<($t0, $t1) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:58:18+2
    assume {:print "$at(14,1170,1172)"} true;
    call $t2 := $ShlU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(14,1170,1172)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(12,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:58:9+13
    assume {:print "$track_return(12,0,0):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:59:5+1
    assume {:print "$at(14,1180,1181)"} true;
L1:

    // return $t2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:59:5+1
    assume {:print "$at(14,1180,1181)"} true;
    $ret0 := $t2;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:59:5+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:59:5+1
    assume {:print "$at(14,1180,1181)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun Simple7::bitshift_right [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple7.move:53:5+70
procedure {:inline 1} $42_Simple7_bitshift_right(_$t0: int, _$t1: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    var $temp_0'u8': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:53:5+1
    assume {:print "$at(14,1032,1033)"} true;
    assume {:print "$track_local(12,1,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:53:5+1
    assume {:print "$track_local(12,1,1):", $t1} $t1 == $t1;

    // $t2 := >>($t0, $t1) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:54:18+2
    assume {:print "$at(14,1091,1093)"} true;
    call $t2 := $ShrU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(14,1091,1093)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(12,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:54:9+13
    assume {:print "$track_return(12,1,0):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:55:5+1
    assume {:print "$at(14,1101,1102)"} true;
L1:

    // return $t2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:55:5+1
    assume {:print "$at(14,1101,1102)"} true;
    $ret0 := $t2;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:55:5+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:55:5+1
    assume {:print "$at(14,1101,1102)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun Simple7::bitshift_right [verification] at /mnt/c/Users/DELL/move-tut/sources/simple7.move:53:5+70
procedure {:timeLimit 40} $42_Simple7_bitshift_right$verify(_$t0: int, _$t1: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    var $temp_0'u8': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:53:5+1
    assume {:print "$at(14,1032,1033)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:53:5+1
    assume $IsValid'u8'($t1);

    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:53:5+1
    assume {:print "$track_local(12,1,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:53:5+1
    assume {:print "$track_local(12,1,1):", $t1} $t1 == $t1;

    // $t2 := >>($t0, $t1) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:54:18+2
    assume {:print "$at(14,1091,1093)"} true;
    call $t2 := $ShrU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(14,1091,1093)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(12,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:54:9+13
    assume {:print "$track_return(12,1,0):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:55:5+1
    assume {:print "$at(14,1101,1102)"} true;
L1:

    // return $t2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:55:5+1
    assume {:print "$at(14,1101,1102)"} true;
    $ret0 := $t2;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:55:5+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:55:5+1
    assume {:print "$at(14,1101,1102)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun Simple7::bitwise_and [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple7.move:16:5+67
procedure {:inline 1} $42_Simple7_bitwise_and(_$t0: int, _$t1: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t2: bv64;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:16:5+1
    assume {:print "$at(14,401,402)"} true;
    assume {:print "$track_local(12,2,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:16:5+1
    assume {:print "$track_local(12,2,1):", $t1} $t1 == $t1;

    // $t2 := &($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:17:18+1
    assume {:print "$at(14,458,459)"} true;
    call $t2 := $AndBv64($int2bv.64($t0), $int2bv.64($t1));

    // trace_return[0]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:17:9+12
    assume {:print "$track_return(12,2,0):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:18:5+1
    assume {:print "$at(14,467,468)"} true;
L1:

    // return $t2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:18:5+1
    assume {:print "$at(14,467,468)"} true;
    $ret0 := $t2;
    return;

}

// fun Simple7::bitwise_and [verification] at /mnt/c/Users/DELL/move-tut/sources/simple7.move:16:5+67
procedure {:timeLimit 40} $42_Simple7_bitwise_and$verify(_$t0: int, _$t1: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t2: bv64;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:16:5+1
    assume {:print "$at(14,401,402)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:16:5+1
    assume $IsValid'u64'($t1);

    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:16:5+1
    assume {:print "$track_local(12,2,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:16:5+1
    assume {:print "$track_local(12,2,1):", $t1} $t1 == $t1;

    // $t2 := &($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:17:18+1
    assume {:print "$at(14,458,459)"} true;
    call $t2 := $AndBv64($int2bv.64($t0), $int2bv.64($t1));

    // trace_return[0]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:17:9+12
    assume {:print "$track_return(12,2,0):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:18:5+1
    assume {:print "$at(14,467,468)"} true;
L1:

    // return $t2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:18:5+1
    assume {:print "$at(14,467,468)"} true;
    $ret0 := $t2;
    return;

}

// fun Simple7::bitwise_or [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple7.move:12:5+66
procedure {:inline 1} $42_Simple7_bitwise_or(_$t0: int, _$t1: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t2: bv64;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:12:5+1
    assume {:print "$at(14,327,328)"} true;
    assume {:print "$track_local(12,3,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:12:5+1
    assume {:print "$track_local(12,3,1):", $t1} $t1 == $t1;

    // $t2 := |($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:13:18+1
    assume {:print "$at(14,383,384)"} true;
    call $t2 := $OrBv64($int2bv.64($t0), $int2bv.64($t1));

    // trace_return[0]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:13:9+12
    assume {:print "$track_return(12,3,0):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:14:5+1
    assume {:print "$at(14,392,393)"} true;
L1:

    // return $t2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:14:5+1
    assume {:print "$at(14,392,393)"} true;
    $ret0 := $t2;
    return;

}

// fun Simple7::bitwise_or [verification] at /mnt/c/Users/DELL/move-tut/sources/simple7.move:12:5+66
procedure {:timeLimit 40} $42_Simple7_bitwise_or$verify(_$t0: int, _$t1: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t2: bv64;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:12:5+1
    assume {:print "$at(14,327,328)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:12:5+1
    assume $IsValid'u64'($t1);

    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:12:5+1
    assume {:print "$track_local(12,3,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:12:5+1
    assume {:print "$track_local(12,3,1):", $t1} $t1 == $t1;

    // $t2 := |($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:13:18+1
    assume {:print "$at(14,383,384)"} true;
    call $t2 := $OrBv64($int2bv.64($t0), $int2bv.64($t1));

    // trace_return[0]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:13:9+12
    assume {:print "$track_return(12,3,0):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:14:5+1
    assume {:print "$at(14,392,393)"} true;
L1:

    // return $t2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:14:5+1
    assume {:print "$at(14,392,393)"} true;
    $ret0 := $t2;
    return;

}

// fun Simple7::bitwise_xor [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple7.move:20:5+67
procedure {:inline 1} $42_Simple7_bitwise_xor(_$t0: int, _$t1: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t2: bv64;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:20:5+1
    assume {:print "$at(14,476,477)"} true;
    assume {:print "$track_local(12,4,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:20:5+1
    assume {:print "$track_local(12,4,1):", $t1} $t1 == $t1;

    // $t2 := ^($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:21:18+1
    assume {:print "$at(14,533,534)"} true;
    call $t2 := $XorBv64($int2bv.64($t0), $int2bv.64($t1));

    // trace_return[0]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:21:9+12
    assume {:print "$track_return(12,4,0):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:22:5+1
    assume {:print "$at(14,542,543)"} true;
L1:

    // return $t2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:22:5+1
    assume {:print "$at(14,542,543)"} true;
    $ret0 := $t2;
    return;

}

// fun Simple7::bitwise_xor [verification] at /mnt/c/Users/DELL/move-tut/sources/simple7.move:20:5+67
procedure {:timeLimit 40} $42_Simple7_bitwise_xor$verify(_$t0: int, _$t1: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t2: bv64;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:20:5+1
    assume {:print "$at(14,476,477)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:20:5+1
    assume $IsValid'u64'($t1);

    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:20:5+1
    assume {:print "$track_local(12,4,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:20:5+1
    assume {:print "$track_local(12,4,1):", $t1} $t1 == $t1;

    // $t2 := ^($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:21:18+1
    assume {:print "$at(14,533,534)"} true;
    call $t2 := $XorBv64($int2bv.64($t0), $int2bv.64($t1));

    // trace_return[0]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:21:9+12
    assume {:print "$track_return(12,4,0):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:22:5+1
    assume {:print "$at(14,542,543)"} true;
L1:

    // return $t2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:22:5+1
    assume {:print "$at(14,542,543)"} true;
    $ret0 := $t2;
    return;

}

// fun Simple7::test_ [verification] at /mnt/c/Users/DELL/move-tut/sources/simple7.move:26:5+208
procedure {:timeLimit 40} $42_Simple7_test_$verify() returns ()
{
    // declare local variables
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: bv64;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: bv64;
    var $t10: int;
    var $t11: int;
    var $t12: bv64;
    var $temp_0'bv64': bv64;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t3 := 7 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:27:29+1
    assume {:print "$at(14,614,615)"} true;
    $t3 := 7;
    assume $IsValid'u64'($t3);

    // $t4 := 4 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:27:32+1
    $t4 := 4;
    assume $IsValid'u64'($t4);

    // $t5 := Simple7::bitwise_or($t3, $t4) on_abort goto L2 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:27:18+16
    call $t5 := $42_Simple7_bitwise_or($t3, $t4);
    if ($abort_flag) {
        assume {:print "$at(14,603,619)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(12,5):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[or]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:27:13+2
    assume {:print "$track_local(12,5,1):", $t5} $t5 == $t5;

    // debug::print<u64>($t5) on_abort goto L2 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:28:9+10
    assume {:print "$at(14,630,640)"} true;
    call $1_debug_print'u64'($t5);
    if ($abort_flag) {
        assume {:print "$at(14,630,640)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(12,5):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t7 := 7 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:30:31+1
    assume {:print "$at(14,683,684)"} true;
    $t7 := 7;
    assume $IsValid'u64'($t7);

    // $t8 := 4 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:30:34+1
    $t8 := 4;
    assume $IsValid'u64'($t8);

    // $t9 := Simple7::bitwise_and($t7, $t8) on_abort goto L2 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:30:19+17
    call $t9 := $42_Simple7_bitwise_and($t7, $t8);
    if ($abort_flag) {
        assume {:print "$at(14,671,688)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(12,5):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[and]($t9) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:30:13+3
    assume {:print "$track_local(12,5,0):", $t9} $t9 == $t9;

    // debug::print<u64>($t9) on_abort goto L2 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:31:9+11
    assume {:print "$at(14,699,710)"} true;
    call $1_debug_print'u64'($t9);
    if ($abort_flag) {
        assume {:print "$at(14,699,710)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(12,5):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t10 := 7 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:33:31+1
    assume {:print "$at(14,745,746)"} true;
    $t10 := 7;
    assume $IsValid'u64'($t10);

    // $t11 := 4 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:33:34+1
    $t11 := 4;
    assume $IsValid'u64'($t11);

    // $t12 := Simple7::bitwise_xor($t10, $t11) on_abort goto L2 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:33:19+17
    call $t12 := $42_Simple7_bitwise_xor($t10, $t11);
    if ($abort_flag) {
        assume {:print "$at(14,733,750)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(12,5):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[xor]($t12) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:33:13+3
    assume {:print "$track_local(12,5,2):", $t12} $t12 == $t12;

    // debug::print<u64>($t12) on_abort goto L2 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:34:9+11
    assume {:print "$at(14,761,772)"} true;
    call $1_debug_print'u64'($t12);
    if ($abort_flag) {
        assume {:print "$at(14,761,772)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(12,5):", $t6} $t6 == $t6;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:35:5+1
    assume {:print "$at(14,779,780)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple7.move:35:5+1
    assume {:print "$at(14,779,780)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:35:5+1
L2:

    // abort($t6) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:35:5+1
    assume {:print "$at(14,779,780)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun Simple7::test_bitShift [verification] at /mnt/c/Users/DELL/move-tut/sources/simple7.move:63:5+161
procedure {:timeLimit 40} $42_Simple7_test_bitShift$verify() returns ()
{
    // declare local variables
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: bv64;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: bv64;
    var $temp_0'bv64': bv64;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t2 := 7 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:64:36+1
    assume {:print "$at(14,1265,1266)"} true;
    $t2 := 7;
    assume $IsValid'u64'($t2);

    // $t3 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:64:39+1
    $t3 := 2;
    assume $IsValid'u8'($t3);

    // $t4 := Simple7::bitshift_right($t2, $t3) on_abort goto L2 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:64:21+20
    call $t4 := $42_Simple7_bitshift_right($t2, $t3);
    if ($abort_flag) {
        assume {:print "$at(14,1250,1270)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(12,6):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_local[right]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:64:13+5
    assume {:print "$track_local(12,6,1):", $t4} $t4 == $t4;

    // debug::print<u64>($t4) on_abort goto L2 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:65:9+13
    assume {:print "$at(14,1281,1294)"} true;
    call $1_debug_print'u64'($t4);
    if ($abort_flag) {
        assume {:print "$at(14,1281,1294)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(12,6):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t6 := 7 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:67:34+1
    assume {:print "$at(14,1332,1333)"} true;
    $t6 := 7;
    assume $IsValid'u64'($t6);

    // $t7 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:67:37+1
    $t7 := 2;
    assume $IsValid'u8'($t7);

    // $t8 := Simple7::bitshift_left($t6, $t7) on_abort goto L2 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:67:20+19
    call $t8 := $42_Simple7_bitshift_left($t6, $t7);
    if ($abort_flag) {
        assume {:print "$at(14,1318,1337)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(12,6):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_local[left]($t8) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:67:13+4
    assume {:print "$track_local(12,6,0):", $t8} $t8 == $t8;

    // debug::print<u64>($t8) on_abort goto L2 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:68:9+12
    assume {:print "$at(14,1348,1360)"} true;
    call $1_debug_print'u64'($t8);
    if ($abort_flag) {
        assume {:print "$at(14,1348,1360)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(12,6):", $t5} $t5 == $t5;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:69:5+1
    assume {:print "$at(14,1367,1368)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple7.move:69:5+1
    assume {:print "$at(14,1367,1368)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple7.move:69:5+1
L2:

    // abort($t5) at /mnt/c/Users/DELL/move-tut/sources/simple7.move:69:5+1
    assume {:print "$at(14,1367,1368)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun Tuples::lots_of_things [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple13.move:5:5+172
procedure {:inline 1} $42_Tuples_lots_of_things() returns ($ret0: bv64, $ret1: Vec (bv8), $ret2: bool)
{
    // declare local variables
    var $t0: int;
    var $t1: Vec (int);
    var $t2: bool;
    var $temp_0'bool': bool;
    var $temp_0'bv64': bv64;
    var $temp_0'vec'bv8'': Vec (bv8);

    // bytecode translation starts here
    // $t0 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple13.move:6:17+1
    assume {:print "$at(7,143,144)"} true;
    $t0 := 0;
    assume $IsValid'u64'($t0);

    // $t1 := [104, 101, 108, 108, 111] at /mnt/c/Users/DELL/move-tut/sources/simple13.move:7:19+8
    assume {:print "$at(7,165,173)"} true;
    $t1 := ConcatVec(MakeVec4(104, 101, 108, 108), MakeVec1(111));
    assume $IsValid'vec'u8''($t1);

    // $t2 := true at /mnt/c/Users/DELL/move-tut/sources/simple13.move:8:22+4
    assume {:print "$at(7,197,201)"} true;
    $t2 := true;
    assume $IsValid'bool'($t2);

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple13.move:10:9+18
    assume {:print "$at(7,222,240)"} true;
    assume {:print "$track_return(13,0,0):", $t0} $t0 == $t0;

    // trace_return[1]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple13.move:10:9+18
    assume {:print "$track_return(13,0,1):", $t1} $t1 == $t1;

    // trace_return[2]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple13.move:10:9+18
    assume {:print "$track_return(13,0,2):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple13.move:11:5+1
    assume {:print "$at(7,247,248)"} true;
L1:

    // return ($t0, $t1, $t2) at /mnt/c/Users/DELL/move-tut/sources/simple13.move:11:5+1
    assume {:print "$at(7,247,248)"} true;
    $ret0 := $t0;
    $ret1 := $t1;
    $ret2 := $t2;
    return;

}

// fun Tuples::lots_of_things [verification] at /mnt/c/Users/DELL/move-tut/sources/simple13.move:5:5+172
procedure {:timeLimit 40} $42_Tuples_lots_of_things$verify() returns ($ret0: bv64, $ret1: Vec (bv8), $ret2: bool)
{
    // declare local variables
    var $t0: int;
    var $t1: Vec (int);
    var $t2: bool;
    var $temp_0'bool': bool;
    var $temp_0'bv64': bv64;
    var $temp_0'vec'bv8'': Vec (bv8);

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple13.move:6:17+1
    assume {:print "$at(7,143,144)"} true;
    $t0 := 0;
    assume $IsValid'u64'($t0);

    // $t1 := [104, 101, 108, 108, 111] at /mnt/c/Users/DELL/move-tut/sources/simple13.move:7:19+8
    assume {:print "$at(7,165,173)"} true;
    $t1 := ConcatVec(MakeVec4(104, 101, 108, 108), MakeVec1(111));
    assume $IsValid'vec'u8''($t1);

    // $t2 := true at /mnt/c/Users/DELL/move-tut/sources/simple13.move:8:22+4
    assume {:print "$at(7,197,201)"} true;
    $t2 := true;
    assume $IsValid'bool'($t2);

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple13.move:10:9+18
    assume {:print "$at(7,222,240)"} true;
    assume {:print "$track_return(13,0,0):", $t0} $t0 == $t0;

    // trace_return[1]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple13.move:10:9+18
    assume {:print "$track_return(13,0,1):", $t1} $t1 == $t1;

    // trace_return[2]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple13.move:10:9+18
    assume {:print "$track_return(13,0,2):", $t2} $t2 == $t2;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple13.move:11:5+1
    assume {:print "$at(7,247,248)"} true;
L1:

    // return ($t0, $t1, $t2) at /mnt/c/Users/DELL/move-tut/sources/simple13.move:11:5+1
    assume {:print "$at(7,247,248)"} true;
    $ret0 := $t0;
    $ret1 := $t1;
    $ret2 := $t2;
    return;

}

// fun Tuples::test_lots_of_things [verification] at /mnt/c/Users/DELL/move-tut/sources/simple13.move:14:5+176
procedure {:timeLimit 40} $42_Tuples_test_lots_of_things$verify() returns ()
{
    // declare local variables
    var $t0: Vec (int);
    var $t1: bool;
    var $t2: int;
    var $t3: bv64;
    var $t4: Vec (bv8);
    var $t5: bool;
    var $t6: int;
    var $temp_0'bool': bool;
    var $temp_0'bv64': bv64;
    var $temp_0'vec'bv8'': Vec (bv8);

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // ($t3, $t4, $t5) := Tuples::lots_of_things() on_abort goto L2 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple13.move:15:34+16
    assume {:print "$at(7,334,350)"} true;
    call $t3,$t4,$t5 := $42_Tuples_lots_of_things();
    if ($abort_flag) {
        assume {:print "$at(7,334,350)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(13,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[trunchy]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple13.move:15:23+7
    assume {:print "$track_local(13,1,1):", $t5} $t5 == $t5;

    // trace_local[name]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple13.move:15:17+4
    assume {:print "$track_local(13,1,0):", $t4} $t4 == $t4;

    // trace_local[x]($t3) at /mnt/c/Users/DELL/move-tut/sources/simple13.move:15:14+1
    assume {:print "$track_local(13,1,2):", $t3} $t3 == $t3;

    // debug::print<u64>($t3) on_abort goto L2 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple13.move:16:9+16
    assume {:print "$at(7,361,377)"} true;
    call $1_debug_print'u64'($t3);
    if ($abort_flag) {
        assume {:print "$at(7,361,377)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(13,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // debug::print<vector<u8>>($t4) on_abort goto L2 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple13.move:17:9+19
    assume {:print "$at(7,388,407)"} true;
    call $1_debug_print'vec'u8''($t4);
    if ($abort_flag) {
        assume {:print "$at(7,388,407)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(13,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // debug::print<bool>($t5) on_abort goto L2 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple13.move:18:9+22
    assume {:print "$at(7,418,440)"} true;
    call $1_debug_print'bool'($t5);
    if ($abort_flag) {
        assume {:print "$at(7,418,440)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(13,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple13.move:19:5+1
    assume {:print "$at(7,447,448)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple13.move:19:5+1
    assume {:print "$at(7,447,448)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple13.move:19:5+1
L2:

    // abort($t6) at /mnt/c/Users/DELL/move-tut/sources/simple13.move:19:5+1
    assume {:print "$at(7,447,448)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// struct simple10::Friends at /mnt/c/Users/DELL/move-tut/sources/simple10.move:5:5+82
datatype $42_simple10_Friends {
    $42_simple10_Friends($people: Vec ($42_simple10_Person))
}
function {:inline} $Update'$42_simple10_Friends'_people(s: $42_simple10_Friends, x: Vec ($42_simple10_Person)): $42_simple10_Friends {
    $42_simple10_Friends(x)
}
function $IsValid'$42_simple10_Friends'(s: $42_simple10_Friends): bool {
    $IsValid'vec'$42_simple10_Person''(s->$people)
}
function {:inline} $IsEqual'$42_simple10_Friends'(s1: $42_simple10_Friends, s2: $42_simple10_Friends): bool {
    $IsEqual'vec'$42_simple10_Person''(s1->$people, s2->$people)}
var $42_simple10_Friends_$memory: $Memory $42_simple10_Friends;

// struct simple10::Person at /mnt/c/Users/DELL/move-tut/sources/simple10.move:10:5+95
datatype $42_simple10_Person {
    $42_simple10_Person($name: Vec (int), $age: int)
}
function {:inline} $Update'$42_simple10_Person'_name(s: $42_simple10_Person, x: Vec (int)): $42_simple10_Person {
    $42_simple10_Person(x, s->$age)
}
function {:inline} $Update'$42_simple10_Person'_age(s: $42_simple10_Person, x: int): $42_simple10_Person {
    $42_simple10_Person(s->$name, x)
}
function $IsValid'$42_simple10_Person'(s: $42_simple10_Person): bool {
    $IsValid'vec'u8''(s->$name)
      && $IsValid'u64'(s->$age)
}
function {:inline} $IsEqual'$42_simple10_Person'(s1: $42_simple10_Person, s2: $42_simple10_Person): bool {
    $IsEqual'vec'u8''(s1->$name, s2->$name)
    && $IsEqual'u64'(s1->$age, s2->$age)}
var $42_simple10_Person_$memory: $Memory $42_simple10_Person;

// fun simple10::add_friend [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple10.move:25:5+127
procedure {:inline 1} $42_simple10_add_friend(_$t0: $42_simple10_Person, _$t1: $Mutation ($42_simple10_Friends)) returns ($ret0: $Mutation ($42_simple10_Friends))
{
    // declare local variables
    var $t2: $Mutation (Vec ($42_simple10_Person));
    var $t3: int;
    var $t0: $42_simple10_Person;
    var $t1: $Mutation ($42_simple10_Friends);
    var $temp_0'$42_simple10_Friends': $42_simple10_Friends;
    var $temp_0'$42_simple10_Person': $42_simple10_Person;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[_person]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:25:5+1
    assume {:print "$at(4,562,563)"} true;
    assume {:print "$track_local(14,0,0):", $t0} $t0 == $t0;

    // trace_local[friends]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:25:5+1
    $temp_0'$42_simple10_Friends' := $Dereference($t1);
    assume {:print "$track_local(14,0,1):", $temp_0'$42_simple10_Friends'} $temp_0'$42_simple10_Friends' == $temp_0'$42_simple10_Friends';

    // $t2 := borrow_field<simple10::Friends>.people($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:26:27+19
    assume {:print "$at(4,653,672)"} true;
    $t2 := $ChildMutation($t1, 0, $Dereference($t1)->$people);

    // vector::push_back<simple10::Person>($t2, $t0) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:26:9+47
    call $t2 := $1_vector_push_back'$42_simple10_Person'($t2, $t0);
    if ($abort_flag) {
        assume {:print "$at(4,635,682)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(14,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // write_back[Reference($t1).people (vector<simple10::Person>)]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:26:9+47
    $t1 := $UpdateMutation($t1, $Update'$42_simple10_Friends'_people($Dereference($t1), $Dereference($t2)));

    // trace_local[friends]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:26:9+47
    $temp_0'$42_simple10_Friends' := $Dereference($t1);
    assume {:print "$track_local(14,0,1):", $temp_0'$42_simple10_Friends'} $temp_0'$42_simple10_Friends' == $temp_0'$42_simple10_Friends';

    // trace_local[friends]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:26:9+47
    $temp_0'$42_simple10_Friends' := $Dereference($t1);
    assume {:print "$track_local(14,0,1):", $temp_0'$42_simple10_Friends'} $temp_0'$42_simple10_Friends' == $temp_0'$42_simple10_Friends';

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:27:5+1
    assume {:print "$at(4,688,689)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple10.move:27:5+1
    assume {:print "$at(4,688,689)"} true;
    $ret0 := $t1;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:27:5+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:27:5+1
    assume {:print "$at(4,688,689)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun simple10::add_friend [verification] at /mnt/c/Users/DELL/move-tut/sources/simple10.move:25:5+127
procedure {:timeLimit 40} $42_simple10_add_friend$verify(_$t0: $42_simple10_Person, _$t1: $Mutation ($42_simple10_Friends)) returns ($ret0: $Mutation ($42_simple10_Friends))
{
    // declare local variables
    var $t2: $Mutation (Vec ($42_simple10_Person));
    var $t3: int;
    var $t0: $42_simple10_Person;
    var $t1: $Mutation ($42_simple10_Friends);
    var $temp_0'$42_simple10_Friends': $42_simple10_Friends;
    var $temp_0'$42_simple10_Person': $42_simple10_Person;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t1->l == $Param(1);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:25:5+1
    assume {:print "$at(4,562,563)"} true;
    assume $IsValid'$42_simple10_Person'($t0);

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:25:5+1
    assume $IsValid'$42_simple10_Friends'($Dereference($t1));

    // trace_local[_person]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:25:5+1
    assume {:print "$track_local(14,0,0):", $t0} $t0 == $t0;

    // trace_local[friends]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:25:5+1
    $temp_0'$42_simple10_Friends' := $Dereference($t1);
    assume {:print "$track_local(14,0,1):", $temp_0'$42_simple10_Friends'} $temp_0'$42_simple10_Friends' == $temp_0'$42_simple10_Friends';

    // $t2 := borrow_field<simple10::Friends>.people($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:26:27+19
    assume {:print "$at(4,653,672)"} true;
    $t2 := $ChildMutation($t1, 0, $Dereference($t1)->$people);

    // vector::push_back<simple10::Person>($t2, $t0) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:26:9+47
    call $t2 := $1_vector_push_back'$42_simple10_Person'($t2, $t0);
    if ($abort_flag) {
        assume {:print "$at(4,635,682)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(14,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // write_back[Reference($t1).people (vector<simple10::Person>)]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:26:9+47
    $t1 := $UpdateMutation($t1, $Update'$42_simple10_Friends'_people($Dereference($t1), $Dereference($t2)));

    // trace_local[friends]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:26:9+47
    $temp_0'$42_simple10_Friends' := $Dereference($t1);
    assume {:print "$track_local(14,0,1):", $temp_0'$42_simple10_Friends'} $temp_0'$42_simple10_Friends' == $temp_0'$42_simple10_Friends';

    // trace_local[friends]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:26:9+47
    $temp_0'$42_simple10_Friends' := $Dereference($t1);
    assume {:print "$track_local(14,0,1):", $temp_0'$42_simple10_Friends'} $temp_0'$42_simple10_Friends' == $temp_0'$42_simple10_Friends';

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:27:5+1
    assume {:print "$at(4,688,689)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple10.move:27:5+1
    assume {:print "$at(4,688,689)"} true;
    $ret0 := $t1;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:27:5+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:27:5+1
    assume {:print "$at(4,688,689)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun simple10::create_friend [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple10.move:16:5+264
procedure {:inline 1} $42_simple10_create_friend(_$t0: $42_simple10_Person, _$t1: $Mutation ($42_simple10_Friends)) returns ($ret0: $42_simple10_Person, $ret1: $Mutation ($42_simple10_Friends))
{
    // declare local variables
    var $t2: $42_simple10_Person;
    var $t3: Vec (int);
    var $t4: int;
    var $t5: $42_simple10_Person;
    var $t6: int;
    var $t0: $42_simple10_Person;
    var $t1: $Mutation ($42_simple10_Friends);
    var $temp_0'$42_simple10_Friends': $42_simple10_Friends;
    var $temp_0'$42_simple10_Person': $42_simple10_Person;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[myFriend]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:16:5+1
    assume {:print "$at(4,290,291)"} true;
    assume {:print "$track_local(14,1,0):", $t0} $t0 == $t0;

    // trace_local[friends]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:16:5+1
    $temp_0'$42_simple10_Friends' := $Dereference($t1);
    assume {:print "$track_local(14,1,1):", $temp_0'$42_simple10_Friends'} $temp_0'$42_simple10_Friends' == $temp_0'$42_simple10_Friends';

    // $t3 := get_field<simple10::Person>.name($t0) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:18:19+13
    assume {:print "$at(4,421,434)"} true;
    $t3 := $t0->$name;

    // $t4 := get_field<simple10::Person>.age($t0) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:19:18+12
    assume {:print "$at(4,454,466)"} true;
    $t4 := $t0->$age;

    // $t5 := pack simple10::Person($t3, $t4) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:17:26+87
    assume {:print "$at(4,392,479)"} true;
    $t5 := $42_simple10_Person($t3, $t4);

    // trace_local[newFriend]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:17:14+9
    assume {:print "$track_local(14,1,2):", $t5} $t5 == $t5;

    // simple10::add_friend($t5, $t1) on_abort goto L2 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:21:9+30
    assume {:print "$at(4,490,520)"} true;
    call $t1 := $42_simple10_add_friend($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(4,490,520)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(14,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_return[0]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:22:9+16
    assume {:print "$at(4,531,547)"} true;
    assume {:print "$track_return(14,1,0):", $t5} $t5 == $t5;

    // trace_local[friends]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:22:9+16
    $temp_0'$42_simple10_Friends' := $Dereference($t1);
    assume {:print "$track_local(14,1,1):", $temp_0'$42_simple10_Friends'} $temp_0'$42_simple10_Friends' == $temp_0'$42_simple10_Friends';

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:23:5+1
    assume {:print "$at(4,553,554)"} true;
L1:

    // return $t5 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:23:5+1
    assume {:print "$at(4,553,554)"} true;
    $ret0 := $t5;
    $ret1 := $t1;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:23:5+1
L2:

    // abort($t6) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:23:5+1
    assume {:print "$at(4,553,554)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun simple10::create_friend [verification] at /mnt/c/Users/DELL/move-tut/sources/simple10.move:16:5+264
procedure {:timeLimit 40} $42_simple10_create_friend$verify(_$t0: $42_simple10_Person, _$t1: $Mutation ($42_simple10_Friends)) returns ($ret0: $42_simple10_Person, $ret1: $Mutation ($42_simple10_Friends))
{
    // declare local variables
    var $t2: $42_simple10_Person;
    var $t3: Vec (int);
    var $t4: int;
    var $t5: $42_simple10_Person;
    var $t6: int;
    var $t0: $42_simple10_Person;
    var $t1: $Mutation ($42_simple10_Friends);
    var $temp_0'$42_simple10_Friends': $42_simple10_Friends;
    var $temp_0'$42_simple10_Person': $42_simple10_Person;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t1->l == $Param(1);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:16:5+1
    assume {:print "$at(4,290,291)"} true;
    assume $IsValid'$42_simple10_Person'($t0);

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:16:5+1
    assume $IsValid'$42_simple10_Friends'($Dereference($t1));

    // trace_local[myFriend]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:16:5+1
    assume {:print "$track_local(14,1,0):", $t0} $t0 == $t0;

    // trace_local[friends]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:16:5+1
    $temp_0'$42_simple10_Friends' := $Dereference($t1);
    assume {:print "$track_local(14,1,1):", $temp_0'$42_simple10_Friends'} $temp_0'$42_simple10_Friends' == $temp_0'$42_simple10_Friends';

    // $t3 := get_field<simple10::Person>.name($t0) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:18:19+13
    assume {:print "$at(4,421,434)"} true;
    $t3 := $t0->$name;

    // $t4 := get_field<simple10::Person>.age($t0) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:19:18+12
    assume {:print "$at(4,454,466)"} true;
    $t4 := $t0->$age;

    // $t5 := pack simple10::Person($t3, $t4) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:17:26+87
    assume {:print "$at(4,392,479)"} true;
    $t5 := $42_simple10_Person($t3, $t4);

    // trace_local[newFriend]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:17:14+9
    assume {:print "$track_local(14,1,2):", $t5} $t5 == $t5;

    // simple10::add_friend($t5, $t1) on_abort goto L2 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:21:9+30
    assume {:print "$at(4,490,520)"} true;
    call $t1 := $42_simple10_add_friend($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(4,490,520)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(14,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_return[0]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:22:9+16
    assume {:print "$at(4,531,547)"} true;
    assume {:print "$track_return(14,1,0):", $t5} $t5 == $t5;

    // trace_local[friends]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:22:9+16
    $temp_0'$42_simple10_Friends' := $Dereference($t1);
    assume {:print "$track_local(14,1,1):", $temp_0'$42_simple10_Friends'} $temp_0'$42_simple10_Friends' == $temp_0'$42_simple10_Friends';

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:23:5+1
    assume {:print "$at(4,553,554)"} true;
L1:

    // return $t5 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:23:5+1
    assume {:print "$at(4,553,554)"} true;
    $ret0 := $t5;
    $ret1 := $t1;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:23:5+1
L2:

    // abort($t6) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:23:5+1
    assume {:print "$at(4,553,554)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun simple10::test_create_friend [verification] at /mnt/c/Users/DELL/move-tut/sources/simple10.move:31:5+340
procedure {:timeLimit 40} $42_simple10_test_create_friend$verify() returns ()
{
    // declare local variables
    var $t0: $42_simple10_Person;
    var $t1: $42_simple10_Person;
    var $t2: $42_simple10_Friends;
    var $t3: Vec (int);
    var $t4: int;
    var $t5: $42_simple10_Person;
    var $t6: Vec ($42_simple10_Person);
    var $t7: int;
    var $t8: $Mutation (Vec ($42_simple10_Person));
    var $t9: $Mutation ($42_simple10_Friends);
    var $t10: $42_simple10_Person;
    var $t11: Vec (int);
    var $t12: Vec (int);
    var $t13: bool;
    var $t14: int;
    var $temp_0'$42_simple10_Friends': $42_simple10_Friends;
    var $temp_0'$42_simple10_Person': $42_simple10_Person;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t3 := [99, 104, 97, 111, 115] at /mnt/c/Users/DELL/move-tut/sources/simple10.move:33:19+8
    assume {:print "$at(4,791,799)"} true;
    $t3 := ConcatVec(MakeVec4(99, 104, 97, 111), MakeVec1(115));
    assume $IsValid'vec'u8''($t3);

    // $t4 := 21 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:34:18+2
    assume {:print "$at(4,819,821)"} true;
    $t4 := 21;
    assume $IsValid'u64'($t4);

    // $t5 := pack simple10::Person($t3, $t4) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:32:21+70
    assume {:print "$at(4,763,833)"} true;
    $t5 := $42_simple10_Person($t3, $t4);

    // trace_local[chaos]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:32:13+5
    assume {:print "$track_local(14,2,0):", $t5} $t5 == $t5;

    // $t6 := vector::empty<simple10::Person>() on_abort goto L4 with $t7 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:38:22+15
    assume {:print "$at(4,892,907)"} true;
    call $t6 := $1_vector_empty'$42_simple10_Person'();
    if ($abort_flag) {
        assume {:print "$at(4,892,907)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(14,2):", $t7} $t7 == $t7;
        goto L4;
    }

    // $t8 := borrow_local($t6) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:38:22+15
    $t8 := $Mutation($Local(6), EmptyVec(), $t6);

    // vector::push_back<simple10::Person>($t8, $t5) on_abort goto L4 with $t7 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:38:22+15
    call $t8 := $1_vector_push_back'$42_simple10_Person'($t8, $t5);
    if ($abort_flag) {
        assume {:print "$at(4,892,907)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(14,2):", $t7} $t7 == $t7;
        goto L4;
    }

    // write_back[LocalRoot($t6)@]($t8) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:38:22+15
    $t6 := $Dereference($t8);

    // $t2 := pack simple10::Friends($t6) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:37:23+58
    assume {:print "$at(4,860,918)"} true;
    $t2 := $42_simple10_Friends($t6);

    // trace_local[friends]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:37:13+7
    assume {:print "$track_local(14,2,2):", $t2} $t2 == $t2;

    // $t9 := borrow_local($t2) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:41:49+12
    assume {:print "$at(4,979,991)"} true;
    $t9 := $Mutation($Local(2), EmptyVec(), $t2);

    // $t10 := simple10::create_friend($t5, $t9) on_abort goto L4 with $t7 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:41:28+34
    call $t10,$t9 := $42_simple10_create_friend($t5, $t9);
    if ($abort_flag) {
        assume {:print "$at(4,958,992)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(14,2):", $t7} $t7 == $t7;
        goto L4;
    }

    // write_back[LocalRoot($t2)@]($t9) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:41:28+34
    $t2 := $Dereference($t9);

    // trace_local[friends]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:41:28+34
    assume {:print "$track_local(14,2,2):", $t2} $t2 == $t2;

    // trace_local[createFriend]($t10) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:41:13+12
    assume {:print "$track_local(14,2,1):", $t10} $t10 == $t10;

    // $t11 := get_field<simple10::Person>.name($t10) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:43:17+17
    assume {:print "$at(4,1013,1030)"} true;
    $t11 := $t10->$name;

    // $t12 := [99, 104, 97, 111, 115] at /mnt/c/Users/DELL/move-tut/sources/simple10.move:43:38+8
    $t12 := ConcatVec(MakeVec4(99, 104, 97, 111), MakeVec1(115));
    assume $IsValid'vec'u8''($t12);

    // $t13 := ==($t11, $t12) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:43:35+2
    $t13 := $IsEqual'vec'u8''($t11, $t12);

    // if ($t13) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:43:9+42
    if ($t13) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:43:9+42
L1:

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:43:9+42
    assume {:print "$at(4,1005,1047)"} true;
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:43:49+1
L0:

    // $t14 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:43:49+1
    assume {:print "$at(4,1045,1046)"} true;
    $t14 := 0;
    assume $IsValid'u64'($t14);

    // trace_abort($t14) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:43:9+42
    assume {:print "$at(4,1005,1047)"} true;
    assume {:print "$track_abort(14,2):", $t14} $t14 == $t14;

    // $t7 := move($t14) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:43:9+42
    $t7 := $t14;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:43:9+42
    goto L4;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:43:51+1
L2:

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:44:5+1
    assume {:print "$at(4,1054,1055)"} true;
L3:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple10.move:44:5+1
    assume {:print "$at(4,1054,1055)"} true;
    return;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple10.move:44:5+1
L4:

    // abort($t7) at /mnt/c/Users/DELL/move-tut/sources/simple10.move:44:5+1
    assume {:print "$at(4,1054,1055)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// struct simple11::Employee at /mnt/c/Users/DELL/move-tut/sources/simple11.move:11:5+119
datatype $42_simple11_Employee {
    $42_simple11_Employee($name: Vec (int), $age: int, $income: bv64)
}
function {:inline} $Update'$42_simple11_Employee'_name(s: $42_simple11_Employee, x: Vec (int)): $42_simple11_Employee {
    $42_simple11_Employee(x, s->$age, s->$income)
}
function {:inline} $Update'$42_simple11_Employee'_age(s: $42_simple11_Employee, x: int): $42_simple11_Employee {
    $42_simple11_Employee(s->$name, x, s->$income)
}
function {:inline} $Update'$42_simple11_Employee'_income(s: $42_simple11_Employee, x: bv64): $42_simple11_Employee {
    $42_simple11_Employee(s->$name, s->$age, x)
}
function $IsValid'$42_simple11_Employee'(s: $42_simple11_Employee): bool {
    $IsValid'vec'u8''(s->$name)
      && $IsValid'u8'(s->$age)
      && $IsValid'bv64'(s->$income)
}
function {:inline} $IsEqual'$42_simple11_Employee'(s1: $42_simple11_Employee, s2: $42_simple11_Employee): bool {
    $IsEqual'vec'u8''(s1->$name, s2->$name)
    && $IsEqual'u8'(s1->$age, s2->$age)
    && $IsEqual'bv64'(s1->$income, s2->$income)}
var $42_simple11_Employee_$memory: $Memory $42_simple11_Employee;

// struct simple11::Employees at /mnt/c/Users/DELL/move-tut/sources/simple11.move:7:5+88
datatype $42_simple11_Employees {
    $42_simple11_Employees($people: Vec ($42_simple11_Employee))
}
function {:inline} $Update'$42_simple11_Employees'_people(s: $42_simple11_Employees, x: Vec ($42_simple11_Employee)): $42_simple11_Employees {
    $42_simple11_Employees(x)
}
function $IsValid'$42_simple11_Employees'(s: $42_simple11_Employees): bool {
    $IsValid'vec'$42_simple11_Employee''(s->$people)
}
function {:inline} $IsEqual'$42_simple11_Employees'(s1: $42_simple11_Employees, s2: $42_simple11_Employees): bool {
    $IsEqual'vec'$42_simple11_Employee''(s1->$people, s2->$people)}
var $42_simple11_Employees_$memory: $Memory $42_simple11_Employees;

// fun simple11::add_employee [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:27:5+138
procedure {:inline 1} $42_simple11_add_employee(_$t0: $Mutation ($42_simple11_Employees), _$t1: $42_simple11_Employee) returns ($ret0: $Mutation ($42_simple11_Employees))
{
    // declare local variables
    var $t2: $Mutation (Vec ($42_simple11_Employee));
    var $t3: int;
    var $t0: $Mutation ($42_simple11_Employees);
    var $t1: $42_simple11_Employee;
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'$42_simple11_Employees': $42_simple11_Employees;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[_employees]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:27:5+1
    assume {:print "$at(5,683,684)"} true;
    $temp_0'$42_simple11_Employees' := $Dereference($t0);
    assume {:print "$track_local(15,0,0):", $temp_0'$42_simple11_Employees'} $temp_0'$42_simple11_Employees' == $temp_0'$42_simple11_Employees';

    // trace_local[_employee]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:27:5+1
    assume {:print "$track_local(15,0,1):", $t1} $t1 == $t1;

    // $t2 := borrow_field<simple11::Employees>.people($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:28:28+22
    assume {:print "$at(5,779,801)"} true;
    $t2 := $ChildMutation($t0, 0, $Dereference($t0)->$people);

    // vector::push_back<simple11::Employee>($t2, $t1) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:28:10+52
    call $t2 := $1_vector_push_back'$42_simple11_Employee'($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(5,761,813)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(15,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // write_back[Reference($t0).people (vector<simple11::Employee>)]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:28:10+52
    $t0 := $UpdateMutation($t0, $Update'$42_simple11_Employees'_people($Dereference($t0), $Dereference($t2)));

    // trace_local[_employees]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:28:10+52
    $temp_0'$42_simple11_Employees' := $Dereference($t0);
    assume {:print "$track_local(15,0,0):", $temp_0'$42_simple11_Employees'} $temp_0'$42_simple11_Employees' == $temp_0'$42_simple11_Employees';

    // trace_local[_employees]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:28:62+1
    $temp_0'$42_simple11_Employees' := $Dereference($t0);
    assume {:print "$track_local(15,0,0):", $temp_0'$42_simple11_Employees'} $temp_0'$42_simple11_Employees' == $temp_0'$42_simple11_Employees';

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:29:5+1
    assume {:print "$at(5,820,821)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple11.move:29:5+1
    assume {:print "$at(5,820,821)"} true;
    $ret0 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:29:5+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:29:5+1
    assume {:print "$at(5,820,821)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun simple11::add_employee [verification] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:27:5+138
procedure {:timeLimit 40} $42_simple11_add_employee$verify(_$t0: $Mutation ($42_simple11_Employees), _$t1: $42_simple11_Employee) returns ($ret0: $Mutation ($42_simple11_Employees))
{
    // declare local variables
    var $t2: $Mutation (Vec ($42_simple11_Employee));
    var $t3: int;
    var $t0: $Mutation ($42_simple11_Employees);
    var $t1: $42_simple11_Employee;
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'$42_simple11_Employees': $42_simple11_Employees;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:27:5+1
    assume {:print "$at(5,683,684)"} true;
    assume $IsValid'$42_simple11_Employees'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:27:5+1
    assume $IsValid'$42_simple11_Employee'($t1);

    // trace_local[_employees]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:27:5+1
    $temp_0'$42_simple11_Employees' := $Dereference($t0);
    assume {:print "$track_local(15,0,0):", $temp_0'$42_simple11_Employees'} $temp_0'$42_simple11_Employees' == $temp_0'$42_simple11_Employees';

    // trace_local[_employee]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:27:5+1
    assume {:print "$track_local(15,0,1):", $t1} $t1 == $t1;

    // $t2 := borrow_field<simple11::Employees>.people($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:28:28+22
    assume {:print "$at(5,779,801)"} true;
    $t2 := $ChildMutation($t0, 0, $Dereference($t0)->$people);

    // vector::push_back<simple11::Employee>($t2, $t1) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:28:10+52
    call $t2 := $1_vector_push_back'$42_simple11_Employee'($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(5,761,813)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(15,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // write_back[Reference($t0).people (vector<simple11::Employee>)]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:28:10+52
    $t0 := $UpdateMutation($t0, $Update'$42_simple11_Employees'_people($Dereference($t0), $Dereference($t2)));

    // trace_local[_employees]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:28:10+52
    $temp_0'$42_simple11_Employees' := $Dereference($t0);
    assume {:print "$track_local(15,0,0):", $temp_0'$42_simple11_Employees'} $temp_0'$42_simple11_Employees' == $temp_0'$42_simple11_Employees';

    // trace_local[_employees]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:28:62+1
    $temp_0'$42_simple11_Employees' := $Dereference($t0);
    assume {:print "$track_local(15,0,0):", $temp_0'$42_simple11_Employees'} $temp_0'$42_simple11_Employees' == $temp_0'$42_simple11_Employees';

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:29:5+1
    assume {:print "$at(5,820,821)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple11.move:29:5+1
    assume {:print "$at(5,820,821)"} true;
    $ret0 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:29:5+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:29:5+1
    assume {:print "$at(5,820,821)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun simple11::create_employee [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:17:5+328
procedure {:inline 1} $42_simple11_create_employee(_$t0: $42_simple11_Employee, _$t1: $Mutation ($42_simple11_Employees)) returns ($ret0: $42_simple11_Employee, $ret1: $Mutation ($42_simple11_Employees))
{
    // declare local variables
    var $t2: $42_simple11_Employee;
    var $t3: Vec (int);
    var $t4: int;
    var $t5: int;
    var $t6: $42_simple11_Employee;
    var $t7: int;
    var $t0: $42_simple11_Employee;
    var $t1: $Mutation ($42_simple11_Employees);
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'$42_simple11_Employees': $42_simple11_Employees;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[_employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:17:5+1
    assume {:print "$at(5,347,348)"} true;
    assume {:print "$track_local(15,1,0):", $t0} $t0 == $t0;

    // trace_local[_employees]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:17:5+1
    $temp_0'$42_simple11_Employees' := $Dereference($t1);
    assume {:print "$track_local(15,1,1):", $temp_0'$42_simple11_Employees'} $temp_0'$42_simple11_Employees' == $temp_0'$42_simple11_Employees';

    // $t3 := get_field<simple11::Employee>.name($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:19:19+14
    assume {:print "$at(5,493,507)"} true;
    $t3 := $t0->$name;

    // $t4 := get_field<simple11::Employee>.age($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:20:18+13
    assume {:print "$at(5,527,540)"} true;
    $t4 := $t0->$age;

    // $t5 := get_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:21:21+16
    assume {:print "$at(5,563,579)"} true;
    $t5 := $t0->$income;

    // $t6 := pack simple11::Employee($t3, $t4, $t5) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:18:27+128
    assume {:print "$at(5,463,591)"} true;
    $t6 := $42_simple11_Employee($t3, $t4, $t5);

    // trace_local[newEmployee]($t6) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:18:13+11
    assume {:print "$track_local(15,1,2):", $t6} $t6 == $t6;

    // simple11::add_employee($t1, $t6) on_abort goto L2 with $t7 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:23:9+37
    assume {:print "$at(5,602,639)"} true;
    call $t1 := $42_simple11_add_employee($t1, $t6);
    if ($abort_flag) {
        assume {:print "$at(5,602,639)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(15,1):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_return[0]($t6) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:24:9+18
    assume {:print "$at(5,650,668)"} true;
    assume {:print "$track_return(15,1,0):", $t6} $t6 == $t6;

    // trace_local[_employees]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:24:9+18
    $temp_0'$42_simple11_Employees' := $Dereference($t1);
    assume {:print "$track_local(15,1,1):", $temp_0'$42_simple11_Employees'} $temp_0'$42_simple11_Employees' == $temp_0'$42_simple11_Employees';

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:25:5+1
    assume {:print "$at(5,674,675)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:25:5+1
    assume {:print "$at(5,674,675)"} true;
    $ret0 := $t6;
    $ret1 := $t1;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:25:5+1
L2:

    // abort($t7) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:25:5+1
    assume {:print "$at(5,674,675)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun simple11::create_employee [verification] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:17:5+328
procedure {:timeLimit 40} $42_simple11_create_employee$verify(_$t0: $42_simple11_Employee, _$t1: $Mutation ($42_simple11_Employees)) returns ($ret0: $42_simple11_Employee, $ret1: $Mutation ($42_simple11_Employees))
{
    // declare local variables
    var $t2: $42_simple11_Employee;
    var $t3: Vec (int);
    var $t4: int;
    var $t5: int;
    var $t6: $42_simple11_Employee;
    var $t7: int;
    var $t0: $42_simple11_Employee;
    var $t1: $Mutation ($42_simple11_Employees);
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'$42_simple11_Employees': $42_simple11_Employees;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t1->l == $Param(1);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:17:5+1
    assume {:print "$at(5,347,348)"} true;
    assume $IsValid'$42_simple11_Employee'($t0);

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:17:5+1
    assume $IsValid'$42_simple11_Employees'($Dereference($t1));

    // trace_local[_employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:17:5+1
    assume {:print "$track_local(15,1,0):", $t0} $t0 == $t0;

    // trace_local[_employees]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:17:5+1
    $temp_0'$42_simple11_Employees' := $Dereference($t1);
    assume {:print "$track_local(15,1,1):", $temp_0'$42_simple11_Employees'} $temp_0'$42_simple11_Employees' == $temp_0'$42_simple11_Employees';

    // $t3 := get_field<simple11::Employee>.name($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:19:19+14
    assume {:print "$at(5,493,507)"} true;
    $t3 := $t0->$name;

    // $t4 := get_field<simple11::Employee>.age($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:20:18+13
    assume {:print "$at(5,527,540)"} true;
    $t4 := $t0->$age;

    // $t5 := get_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:21:21+16
    assume {:print "$at(5,563,579)"} true;
    $t5 := $t0->$income;

    // $t6 := pack simple11::Employee($t3, $t4, $t5) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:18:27+128
    assume {:print "$at(5,463,591)"} true;
    $t6 := $42_simple11_Employee($t3, $t4, $t5);

    // trace_local[newEmployee]($t6) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:18:13+11
    assume {:print "$track_local(15,1,2):", $t6} $t6 == $t6;

    // simple11::add_employee($t1, $t6) on_abort goto L2 with $t7 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:23:9+37
    assume {:print "$at(5,602,639)"} true;
    call $t1 := $42_simple11_add_employee($t1, $t6);
    if ($abort_flag) {
        assume {:print "$at(5,602,639)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(15,1):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_return[0]($t6) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:24:9+18
    assume {:print "$at(5,650,668)"} true;
    assume {:print "$track_return(15,1,0):", $t6} $t6 == $t6;

    // trace_local[_employees]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:24:9+18
    $temp_0'$42_simple11_Employees' := $Dereference($t1);
    assume {:print "$track_local(15,1,1):", $temp_0'$42_simple11_Employees'} $temp_0'$42_simple11_Employees' == $temp_0'$42_simple11_Employees';

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:25:5+1
    assume {:print "$at(5,674,675)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:25:5+1
    assume {:print "$at(5,674,675)"} true;
    $ret0 := $t6;
    $ret1 := $t1;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:25:5+1
L2:

    // abort($t7) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:25:5+1
    assume {:print "$at(5,674,675)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun simple11::decrease_income [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:36:5+174
procedure {:inline 1} $42_simple11_decrease_income(_$t0: $Mutation ($42_simple11_Employee), _$t1: int) returns ($ret0: $Mutation ($42_simple11_Employee), $ret1: $Mutation ($42_simple11_Employee))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: $Mutation (int);
    var $t6: $Mutation ($42_simple11_Employee);
    var $t0: $Mutation ($42_simple11_Employee);
    var $t1: int;
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:36:5+1
    assume {:print "$at(5,1005,1006)"} true;
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,2,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_local[penality]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:36:5+1
    assume {:print "$track_local(15,2,1):", $t1} $t1 == $t1;

    // $t2 := get_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:37:29+15
    assume {:print "$at(5,1118,1133)"} true;
    $t2 := $Dereference($t0)->$income;

    // $t3 := -($t2, $t1) on_abort goto L2 with $t4 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:37:45+1
    call $t3 := $Sub($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(5,1134,1135)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,2):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := borrow_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:37:11+15
    $t5 := $ChildMutation($t0, 2, $Dereference($t0)->$income);

    // write_ref($t5, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:37:11+44
    $t5 := $UpdateMutation($t5, $t3);

    // write_back[Reference($t0).income (u64)]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:37:11+44
    $t0 := $UpdateMutation($t0, $Update'$42_simple11_Employee'_income($Dereference($t0), $Dereference($t5)));

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:37:11+44
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,2,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:38:11+15
    assume {:print "$at(5,1157,1172)"} true;
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_return(15,2,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:38:11+15
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,2,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // $t6 := move($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:38:11+15
    $t6 := $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:39:5+1
    assume {:print "$at(5,1178,1179)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:39:5+1
    assume {:print "$at(5,1178,1179)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:39:5+1
L2:

    // abort($t4) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:39:5+1
    assume {:print "$at(5,1178,1179)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun simple11::decrease_income [verification] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:36:5+174
procedure {:timeLimit 40} $42_simple11_decrease_income$verify(_$t0: $Mutation ($42_simple11_Employee), _$t1: int) returns ($ret0: $Mutation ($42_simple11_Employee), $ret1: $Mutation ($42_simple11_Employee))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: $Mutation (int);
    var $t6: $Mutation ($42_simple11_Employee);
    var $t0: $Mutation ($42_simple11_Employee);
    var $t1: int;
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:36:5+1
    assume {:print "$at(5,1005,1006)"} true;
    assume $IsValid'$42_simple11_Employee'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:36:5+1
    assume $IsValid'u64'($t1);

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:36:5+1
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,2,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_local[penality]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:36:5+1
    assume {:print "$track_local(15,2,1):", $t1} $t1 == $t1;

    // $t2 := get_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:37:29+15
    assume {:print "$at(5,1118,1133)"} true;
    $t2 := $Dereference($t0)->$income;

    // $t3 := -($t2, $t1) on_abort goto L2 with $t4 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:37:45+1
    call $t3 := $Sub($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(5,1134,1135)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,2):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := borrow_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:37:11+15
    $t5 := $ChildMutation($t0, 2, $Dereference($t0)->$income);

    // write_ref($t5, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:37:11+44
    $t5 := $UpdateMutation($t5, $t3);

    // write_back[Reference($t0).income (u64)]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:37:11+44
    $t0 := $UpdateMutation($t0, $Update'$42_simple11_Employee'_income($Dereference($t0), $Dereference($t5)));

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:37:11+44
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,2,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:38:11+15
    assume {:print "$at(5,1157,1172)"} true;
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_return(15,2,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:38:11+15
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,2,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // $t6 := move($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:38:11+15
    $t6 := $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:39:5+1
    assume {:print "$at(5,1178,1179)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:39:5+1
    assume {:print "$at(5,1178,1179)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:39:5+1
L2:

    // abort($t4) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:39:5+1
    assume {:print "$at(5,1178,1179)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun simple11::div_income [verification] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:46:5+168
procedure {:timeLimit 40} $42_simple11_div_income$verify(_$t0: $Mutation ($42_simple11_Employee), _$t1: int) returns ($ret0: $Mutation ($42_simple11_Employee), $ret1: $Mutation ($42_simple11_Employee))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: $Mutation (int);
    var $t6: $Mutation ($42_simple11_Employee);
    var $t0: $Mutation ($42_simple11_Employee);
    var $t1: int;
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:46:5+1
    assume {:print "$at(5,1366,1367)"} true;
    assume $IsValid'$42_simple11_Employee'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:46:5+1
    assume $IsValid'u64'($t1);

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:46:5+1
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,3,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_local[divisor]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:46:5+1
    assume {:print "$track_local(15,3,1):", $t1} $t1 == $t1;

    // $t2 := get_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:47:29+15
    assume {:print "$at(5,1474,1489)"} true;
    $t2 := $Dereference($t0)->$income;

    // $t3 := /($t2, $t1) on_abort goto L2 with $t4 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:47:45+1
    call $t3 := $Div($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(5,1490,1491)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,3):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := borrow_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:47:11+15
    $t5 := $ChildMutation($t0, 2, $Dereference($t0)->$income);

    // write_ref($t5, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:47:11+43
    $t5 := $UpdateMutation($t5, $t3);

    // write_back[Reference($t0).income (u64)]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:47:11+43
    $t0 := $UpdateMutation($t0, $Update'$42_simple11_Employee'_income($Dereference($t0), $Dereference($t5)));

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:47:11+43
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,3,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:48:11+15
    assume {:print "$at(5,1512,1527)"} true;
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_return(15,3,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:48:11+15
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,3,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // $t6 := move($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:48:11+15
    $t6 := $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:49:5+1
    assume {:print "$at(5,1533,1534)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:49:5+1
    assume {:print "$at(5,1533,1534)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:49:5+1
L2:

    // abort($t4) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:49:5+1
    assume {:print "$at(5,1533,1534)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun simple11::increase_income [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:31:5+168
procedure {:inline 1} $42_simple11_increase_income(_$t0: $Mutation ($42_simple11_Employee), _$t1: int) returns ($ret0: $Mutation ($42_simple11_Employee), $ret1: $Mutation ($42_simple11_Employee))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: $Mutation (int);
    var $t6: $Mutation ($42_simple11_Employee);
    var $t0: $Mutation ($42_simple11_Employee);
    var $t1: int;
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:31:5+1
    assume {:print "$at(5,829,830)"} true;
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,4,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_local[bonus]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:31:5+1
    assume {:print "$track_local(15,4,1):", $t1} $t1 == $t1;

    // $t2 := get_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:32:29+15
    assume {:print "$at(5,939,954)"} true;
    $t2 := $Dereference($t0)->$income;

    // $t3 := +($t2, $t1) on_abort goto L2 with $t4 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:32:45+1
    call $t3 := $AddU64($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(5,955,956)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,4):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := borrow_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:32:11+15
    $t5 := $ChildMutation($t0, 2, $Dereference($t0)->$income);

    // write_ref($t5, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:32:11+41
    $t5 := $UpdateMutation($t5, $t3);

    // write_back[Reference($t0).income (u64)]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:32:11+41
    $t0 := $UpdateMutation($t0, $Update'$42_simple11_Employee'_income($Dereference($t0), $Dereference($t5)));

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:32:11+41
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,4,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:33:11+15
    assume {:print "$at(5,975,990)"} true;
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_return(15,4,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:33:11+15
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,4,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // $t6 := move($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:33:11+15
    $t6 := $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:34:5+1
    assume {:print "$at(5,996,997)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:34:5+1
    assume {:print "$at(5,996,997)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:34:5+1
L2:

    // abort($t4) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:34:5+1
    assume {:print "$at(5,996,997)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun simple11::increase_income [verification] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:31:5+168
procedure {:timeLimit 40} $42_simple11_increase_income$verify(_$t0: $Mutation ($42_simple11_Employee), _$t1: int) returns ($ret0: $Mutation ($42_simple11_Employee), $ret1: $Mutation ($42_simple11_Employee))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: $Mutation (int);
    var $t6: $Mutation ($42_simple11_Employee);
    var $t0: $Mutation ($42_simple11_Employee);
    var $t1: int;
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:31:5+1
    assume {:print "$at(5,829,830)"} true;
    assume $IsValid'$42_simple11_Employee'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:31:5+1
    assume $IsValid'u64'($t1);

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:31:5+1
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,4,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_local[bonus]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:31:5+1
    assume {:print "$track_local(15,4,1):", $t1} $t1 == $t1;

    // $t2 := get_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:32:29+15
    assume {:print "$at(5,939,954)"} true;
    $t2 := $Dereference($t0)->$income;

    // $t3 := +($t2, $t1) on_abort goto L2 with $t4 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:32:45+1
    call $t3 := $AddU64($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(5,955,956)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,4):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := borrow_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:32:11+15
    $t5 := $ChildMutation($t0, 2, $Dereference($t0)->$income);

    // write_ref($t5, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:32:11+41
    $t5 := $UpdateMutation($t5, $t3);

    // write_back[Reference($t0).income (u64)]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:32:11+41
    $t0 := $UpdateMutation($t0, $Update'$42_simple11_Employee'_income($Dereference($t0), $Dereference($t5)));

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:32:11+41
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,4,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:33:11+15
    assume {:print "$at(5,975,990)"} true;
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_return(15,4,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:33:11+15
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,4,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // $t6 := move($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:33:11+15
    $t6 := $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:34:5+1
    assume {:print "$at(5,996,997)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:34:5+1
    assume {:print "$at(5,996,997)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:34:5+1
L2:

    // abort($t4) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:34:5+1
    assume {:print "$at(5,996,997)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun simple11::is_employee_age_even [verification] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:51:5+242
procedure {:timeLimit 40} $42_simple11_is_employee_age_even$verify(_$t0: $42_simple11_Employee) returns ($ret0: bool)
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: bool;
    var $t9: bool;
    var $t0: $42_simple11_Employee;
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'bool': bool;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:51:5+1
    assume {:print "$at(5,1542,1543)"} true;
    assume $IsValid'$42_simple11_Employee'($t0);

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:51:5+1
    assume {:print "$track_local(15,5,0):", $t0} $t0 == $t0;

    // $t2 := get_field<simple11::Employee>.age($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:53:13+12
    assume {:print "$at(5,1645,1657)"} true;
    $t2 := $t0->$age;

    // $t3 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:53:28+1
    $t3 := 2;
    assume $IsValid'u8'($t3);

    // $t4 := %($t2, $t3) on_abort goto L4 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:53:26+1
    call $t4 := $Mod($t2, $t3);
    if ($abort_flag) {
        assume {:print "$at(5,1658,1659)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(15,5):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t6 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:53:33+1
    $t6 := 0;
    assume $IsValid'u8'($t6);

    // $t7 := ==($t4, $t6) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:53:30+2
    $t7 := $IsEqual'u8'($t4, $t6);

    // if ($t7) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:53:9+112
    if ($t7) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:54:22+4
    assume {:print "$at(5,1692,1696)"} true;
L1:

    // $t8 := true at /mnt/c/Users/DELL/move-tut/sources/simple11.move:54:22+4
    assume {:print "$at(5,1692,1696)"} true;
    $t8 := true;
    assume $IsValid'bool'($t8);

    // $t1 := $t8 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:54:13+6
    $t1 := $t8;

    // trace_local[isEven]($t8) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:54:13+6
    assume {:print "$track_local(15,5,1):", $t8} $t8 == $t8;

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:54:13+13
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:56:22+5
    assume {:print "$at(5,1737,1742)"} true;
L0:

    // $t9 := false at /mnt/c/Users/DELL/move-tut/sources/simple11.move:56:22+5
    assume {:print "$at(5,1737,1742)"} true;
    $t9 := false;
    assume $IsValid'bool'($t9);

    // $t1 := $t9 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:56:13+6
    $t1 := $t9;

    // trace_local[isEven]($t9) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:56:13+6
    assume {:print "$track_local(15,5,1):", $t9} $t9 == $t9;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:58:16+6
    assume {:print "$at(5,1771,1777)"} true;
L2:

    // trace_return[0]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:58:9+13
    assume {:print "$at(5,1764,1777)"} true;
    assume {:print "$track_return(15,5,0):", $t1} $t1 == $t1;

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:59:5+1
    assume {:print "$at(5,1783,1784)"} true;
L3:

    // return $t1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:59:5+1
    assume {:print "$at(5,1783,1784)"} true;
    $ret0 := $t1;
    return;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:59:5+1
L4:

    // abort($t5) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:59:5+1
    assume {:print "$at(5,1783,1784)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun simple11::multiply_income [verification] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:41:6+170
procedure {:timeLimit 40} $42_simple11_multiply_income$verify(_$t0: $Mutation ($42_simple11_Employee), _$t1: int) returns ($ret0: $Mutation ($42_simple11_Employee), $ret1: $Mutation ($42_simple11_Employee))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: $Mutation (int);
    var $t6: $Mutation ($42_simple11_Employee);
    var $t0: $Mutation ($42_simple11_Employee);
    var $t1: int;
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:41:6+1
    assume {:print "$at(5,1188,1189)"} true;
    assume $IsValid'$42_simple11_Employee'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:41:6+1
    assume $IsValid'u64'($t1);

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:41:6+1
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,6,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_local[factor]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:41:6+1
    assume {:print "$track_local(15,6,1):", $t1} $t1 == $t1;

    // $t2 := get_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:42:29+15
    assume {:print "$at(5,1299,1314)"} true;
    $t2 := $Dereference($t0)->$income;

    // $t3 := *($t2, $t1) on_abort goto L2 with $t4 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:42:45+1
    call $t3 := $MulU64($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(5,1315,1316)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,6):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := borrow_field<simple11::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:42:11+15
    $t5 := $ChildMutation($t0, 2, $Dereference($t0)->$income);

    // write_ref($t5, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:42:11+42
    $t5 := $UpdateMutation($t5, $t3);

    // write_back[Reference($t0).income (u64)]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:42:11+42
    $t0 := $UpdateMutation($t0, $Update'$42_simple11_Employee'_income($Dereference($t0), $Dereference($t5)));

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:42:11+42
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,6,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:43:11+15
    assume {:print "$at(5,1336,1351)"} true;
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_return(15,6,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:43:11+15
    $temp_0'$42_simple11_Employee' := $Dereference($t0);
    assume {:print "$track_local(15,6,0):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // $t6 := move($t0) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:43:11+15
    $t6 := $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:44:5+1
    assume {:print "$at(5,1357,1358)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:44:5+1
    assume {:print "$at(5,1357,1358)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:44:5+1
L2:

    // abort($t4) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:44:5+1
    assume {:print "$at(5,1357,1358)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun simple11::test_create_employee [verification] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:62:5+470
procedure {:timeLimit 40} $42_simple11_test_create_employee$verify() returns ()
{
    // declare local variables
    var $t0: $42_simple11_Employee;
    var $t1: $42_simple11_Employee;
    var $t2: $42_simple11_Employees;
    var $t3: Vec (int);
    var $t4: int;
    var $t5: int;
    var $t6: $42_simple11_Employee;
    var $t7: Vec ($42_simple11_Employee);
    var $t8: int;
    var $t9: $Mutation (Vec ($42_simple11_Employee));
    var $t10: $Mutation ($42_simple11_Employees);
    var $t11: $42_simple11_Employee;
    var $t12: Vec (int);
    var $t13: Vec (int);
    var $t14: bool;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: bool;
    var $t19: int;
    var $t20: int;
    var $t21: int;
    var $t22: bool;
    var $t23: int;
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'$42_simple11_Employees': $42_simple11_Employees;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t3 := [99, 104, 97, 111, 115] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:64:19+8
    assume {:print "$at(5,1888,1896)"} true;
    $t3 := ConcatVec(MakeVec4(99, 104, 97, 111), MakeVec1(115));
    assume $IsValid'vec'u8''($t3);

    // $t4 := 21 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:65:18+2
    assume {:print "$at(5,1916,1918)"} true;
    $t4 := 21;
    assume $IsValid'u8'($t4);

    // $t5 := 2000 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:66:21+4
    assume {:print "$at(5,1941,1945)"} true;
    $t5 := 2000;
    assume $IsValid'u64'($t5);

    // $t6 := pack simple11::Employee($t3, $t4, $t5) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:63:21+99
    assume {:print "$at(5,1858,1957)"} true;
    $t6 := $42_simple11_Employee($t3, $t4, $t5);

    // trace_local[chaos]($t6) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:63:13+5
    assume {:print "$track_local(15,7,0):", $t6} $t6 == $t6;

    // $t7 := vector::empty<simple11::Employee>() on_abort goto L10 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:69:22+15
    assume {:print "$at(5,2018,2033)"} true;
    call $t7 := $1_vector_empty'$42_simple11_Employee'();
    if ($abort_flag) {
        assume {:print "$at(5,2018,2033)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,7):", $t8} $t8 == $t8;
        goto L10;
    }

    // $t9 := borrow_local($t7) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:69:22+15
    $t9 := $Mutation($Local(7), EmptyVec(), $t7);

    // vector::push_back<simple11::Employee>($t9, $t6) on_abort goto L10 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:69:22+15
    call $t9 := $1_vector_push_back'$42_simple11_Employee'($t9, $t6);
    if ($abort_flag) {
        assume {:print "$at(5,2018,2033)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,7):", $t8} $t8 == $t8;
        goto L10;
    }

    // write_back[LocalRoot($t7)@]($t9) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:69:22+15
    $t7 := $Dereference($t9);

    // $t2 := pack simple11::Employees($t7) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:68:25+60
    assume {:print "$at(5,1984,2044)"} true;
    $t2 := $42_simple11_Employees($t7);

    // trace_local[employees]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:68:13+9
    assume {:print "$track_local(15,7,2):", $t2} $t2 == $t2;

    // $t10 := borrow_local($t2) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:71:54+14
    assume {:print "$at(5,2100,2114)"} true;
    $t10 := $Mutation($Local(2), EmptyVec(), $t2);

    // $t11 := simple11::create_employee($t6, $t10) on_abort goto L10 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:71:31+38
    call $t11,$t10 := $42_simple11_create_employee($t6, $t10);
    if ($abort_flag) {
        assume {:print "$at(5,2077,2115)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,7):", $t8} $t8 == $t8;
        goto L10;
    }

    // write_back[LocalRoot($t2)@]($t10) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:71:31+38
    $t2 := $Dereference($t10);

    // trace_local[employees]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:71:31+38
    assume {:print "$track_local(15,7,2):", $t2} $t2 == $t2;

    // trace_local[createdEmployee]($t11) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:71:13+15
    assume {:print "$track_local(15,7,1):", $t11} $t11 == $t11;

    // $t12 := get_field<simple11::Employee>.name($t11) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:72:17+20
    assume {:print "$at(5,2134,2154)"} true;
    $t12 := $t11->$name;

    // $t13 := [99, 104, 97, 111, 115] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:72:41+8
    $t13 := ConcatVec(MakeVec4(99, 104, 97, 111), MakeVec1(115));
    assume $IsValid'vec'u8''($t13);

    // $t14 := ==($t12, $t13) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:72:38+2
    $t14 := $IsEqual'vec'u8''($t12, $t13);

    // if ($t14) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:72:9+44
    if ($t14) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:72:9+44
L1:

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:72:9+44
    assume {:print "$at(5,2126,2170)"} true;
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:72:51+1
L0:

    // $t15 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:72:51+1
    assume {:print "$at(5,2168,2169)"} true;
    $t15 := 0;
    assume $IsValid'u64'($t15);

    // trace_abort($t15) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:72:9+44
    assume {:print "$at(5,2126,2170)"} true;
    assume {:print "$track_abort(15,7):", $t15} $t15 == $t15;

    // $t8 := move($t15) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:72:9+44
    $t8 := $t15;

    // goto L10 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:72:9+44
    goto L10;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:73:17+15
    assume {:print "$at(5,2189,2204)"} true;
L2:

    // $t16 := get_field<simple11::Employee>.age($t11) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:73:17+19
    assume {:print "$at(5,2189,2208)"} true;
    $t16 := $t11->$age;

    // $t17 := 21 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:73:40+2
    $t17 := 21;
    assume $IsValid'u8'($t17);

    // $t18 := ==($t16, $t17) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:73:37+2
    $t18 := $IsEqual'u8'($t16, $t17);

    // if ($t18) goto L4 else goto L3 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:73:9+37
    if ($t18) { goto L4; } else { goto L3; }

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:73:9+37
L4:

    // goto L5 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:73:9+37
    assume {:print "$at(5,2181,2218)"} true;
    goto L5;

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:73:44+1
L3:

    // $t19 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:73:44+1
    assume {:print "$at(5,2216,2217)"} true;
    $t19 := 0;
    assume $IsValid'u64'($t19);

    // trace_abort($t19) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:73:9+37
    assume {:print "$at(5,2181,2218)"} true;
    assume {:print "$track_abort(15,7):", $t19} $t19 == $t19;

    // $t8 := move($t19) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:73:9+37
    $t8 := $t19;

    // goto L10 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:73:9+37
    goto L10;

    // label L5 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:74:17+15
    assume {:print "$at(5,2237,2252)"} true;
L5:

    // $t20 := get_field<simple11::Employee>.income($t11) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:74:17+22
    assume {:print "$at(5,2237,2259)"} true;
    $t20 := $t11->$income;

    // $t21 := 2000 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:74:43+4
    $t21 := 2000;
    assume $IsValid'u64'($t21);

    // $t22 := ==($t20, $t21) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:74:40+2
    $t22 := $IsEqual'u64'($t20, $t21);

    // if ($t22) goto L7 else goto L6 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:74:9+42
    if ($t22) { goto L7; } else { goto L6; }

    // label L7 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:74:9+42
L7:

    // goto L8 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:74:9+42
    assume {:print "$at(5,2229,2271)"} true;
    goto L8;

    // label L6 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:74:49+1
L6:

    // $t23 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:74:49+1
    assume {:print "$at(5,2269,2270)"} true;
    $t23 := 0;
    assume $IsValid'u64'($t23);

    // trace_abort($t23) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:74:9+42
    assume {:print "$at(5,2229,2271)"} true;
    assume {:print "$track_abort(15,7):", $t23} $t23 == $t23;

    // $t8 := move($t23) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:74:9+42
    $t8 := $t23;

    // goto L10 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:74:9+42
    goto L10;

    // label L8 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:74:9+42
L8:

    // label L9 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:75:5+1
    assume {:print "$at(5,2277,2278)"} true;
L9:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple11.move:75:5+1
    assume {:print "$at(5,2277,2278)"} true;
    return;

    // label L10 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:75:5+1
L10:

    // abort($t8) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:75:5+1
    assume {:print "$at(5,2277,2278)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun simple11::test_decrease_income [verification] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:94:5+478
procedure {:timeLimit 40} $42_simple11_test_decrease_income$verify() returns ()
{
    // declare local variables
    var $t0: $42_simple11_Employee;
    var $t1: $42_simple11_Employee;
    var $t2: $Mutation ($42_simple11_Employee);
    var $t3: $42_simple11_Employees;
    var $t4: Vec (int);
    var $t5: int;
    var $t6: bv64;
    var $t7: $42_simple11_Employee;
    var $t8: Vec ($42_simple11_Employee);
    var $t9: int;
    var $t10: $Mutation (Vec ($42_simple11_Employee));
    var $t11: $Mutation ($42_simple11_Employees);
    var $t12: $Mutation ($42_simple11_Employee);
    var $t13: int;
    var $t14: $Mutation ($42_simple11_Employee);
    var $t15: bv64;
    var $t16: bv64;
    var $t17: bv64;
    var $t18: bool;
    var $t19: int;
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'$42_simple11_Employees': $42_simple11_Employees;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t4 := [99, 104, 97, 111, 115] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:96:19+8
    assume {:print "$at(5,2844,2852)"} true;
    $t4 := ConcatVec(MakeVec4(99, 104, 97, 111), MakeVec1(115));
    assume $IsValid'vec'u8''($t4);

    // $t5 := 21 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:97:18+2
    assume {:print "$at(5,2872,2874)"} true;
    $t5 := 21;
    assume $IsValid'u8'($t5);

    // $t6 := 2000 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:98:21+4
    assume {:print "$at(5,2897,2901)"} true;
    $t6 := 2000bv64;
    assume $IsValid'bv64'($t6);

    // $t7 := pack simple11::Employee($t4, $t5, $t6) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:95:21+99
    assume {:print "$at(5,2814,2913)"} true;
    $t7 := $42_simple11_Employee($t4, $t5, $t6);

    // trace_local[chaos]($t7) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:95:13+5
    assume {:print "$track_local(15,8,0):", $t7} $t7 == $t7;

    // $t8 := vector::empty<simple11::Employee>() on_abort goto L4 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:102:22+15
    assume {:print "$at(5,2976,2991)"} true;
    call $t8 := $1_vector_empty'$42_simple11_Employee'();
    if ($abort_flag) {
        assume {:print "$at(5,2976,2991)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(15,8):", $t9} $t9 == $t9;
        goto L4;
    }

    // $t10 := borrow_local($t8) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:102:22+15
    $t10 := $Mutation($Local(8), EmptyVec(), $t8);

    // vector::push_back<simple11::Employee>($t10, $t7) on_abort goto L4 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:102:22+15
    call $t10 := $1_vector_push_back'$42_simple11_Employee'($t10, $t7);
    if ($abort_flag) {
        assume {:print "$at(5,2976,2991)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(15,8):", $t9} $t9 == $t9;
        goto L4;
    }

    // write_back[LocalRoot($t8)@]($t10) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:102:22+15
    $t8 := $Dereference($t10);

    // $t3 := pack simple11::Employees($t8) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:101:25+60
    assume {:print "$at(5,2942,3002)"} true;
    $t3 := $42_simple11_Employees($t8);

    // trace_local[employees]($t3) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:101:13+9
    assume {:print "$track_local(15,8,3):", $t3} $t3 == $t3;

    // $t11 := borrow_local($t3) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:105:54+14
    assume {:print "$at(5,3060,3074)"} true;
    $t11 := $Mutation($Local(3), EmptyVec(), $t3);

    // $t1 := simple11::create_employee($t7, $t11) on_abort goto L4 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:105:31+38
    call $t1,$t11 := $42_simple11_create_employee($t7, $t11);
    if ($abort_flag) {
        assume {:print "$at(5,3037,3075)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(15,8):", $t9} $t9 == $t9;
        goto L4;
    }

    // write_back[LocalRoot($t3)@]($t11) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:105:31+38
    $t3 := $Dereference($t11);

    // trace_local[employees]($t3) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:105:31+38
    assume {:print "$track_local(15,8,3):", $t3} $t3 == $t3;

    // trace_local[createdEmployee]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:105:13+15
    assume {:print "$track_local(15,8,1):", $t1} $t1 == $t1;

    // $t12 := borrow_local($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:106:44+20
    assume {:print "$at(5,3121,3141)"} true;
    $t12 := $Mutation($Local(1), EmptyVec(), $t1);

    // $t13 := 50 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:106:66+2
    $t13 := 50;
    assume $IsValid'u64'($t13);

    // $t14 := simple11::decrease_income($t12, $t13) on_abort goto L4 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:106:28+41
    call $t14,$t12 := $42_simple11_decrease_income($t12, $t13);
    if ($abort_flag) {
        assume {:print "$at(5,3105,3146)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(15,8):", $t9} $t9 == $t9;
        goto L4;
    }

    // trace_local[decreasedEmp]($t14) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:106:13+12
    $temp_0'$42_simple11_Employee' := $Dereference($t14);
    assume {:print "$track_local(15,8,2):", $temp_0'$42_simple11_Employee'} $temp_0'$42_simple11_Employee' == $temp_0'$42_simple11_Employee';

    // $t15 := get_field<simple11::Employee>.income($t14) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:107:15+20
    assume {:print "$at(5,3163,3183)"} true;
    $t15 := $Dereference($t14)->$income;

    // debug::print<u64>($t15) on_abort goto L4 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:107:9+27
    call $1_debug_print'u64'($t15);
    if ($abort_flag) {
        assume {:print "$at(5,3157,3184)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(15,8):", $t9} $t9 == $t9;
        goto L4;
    }

    // $t16 := get_field<simple11::Employee>.income($t14) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:17+19
    assume {:print "$at(5,3203,3222)"} true;
    $t16 := $Dereference($t14)->$income;

    // write_back[LocalRoot($t1)@]($t12) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:17+19
    $t1 := $Dereference($t12);

    // trace_local[createdEmployee]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:17+19
    assume {:print "$track_local(15,8,1):", $t1} $t1 == $t1;

    // $t17 := 1950 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:40+4
    $t17 := 1950bv64;
    assume $IsValid'bv64'($t17);

    // $t18 := ==($t16, $t17) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:37+2
    $t18 := $IsEqual'bv64'($t16, $t17);

    // if ($t18) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:9+40
    if ($t18) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:9+40
L1:

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:9+40
    assume {:print "$at(5,3195,3235)"} true;
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:47+1
L0:

    // $t19 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:47+1
    assume {:print "$at(5,3233,3234)"} true;
    $t19 := 0;
    assume $IsValid'u64'($t19);

    // trace_abort($t19) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:9+40
    assume {:print "$at(5,3195,3235)"} true;
    assume {:print "$track_abort(15,8):", $t19} $t19 == $t19;

    // $t9 := move($t19) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:9+40
    $t9 := $t19;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:9+40
    goto L4;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:108:9+40
L2:

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:109:5+1
    assume {:print "$at(5,3241,3242)"} true;
L3:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple11.move:109:5+1
    assume {:print "$at(5,3241,3242)"} true;
    return;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:109:5+1
L4:

    // abort($t9) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:109:5+1
    assume {:print "$at(5,3241,3242)"} true;
    $abort_code := $t9;
    $abort_flag := true;
    return;

}

// fun simple11::test_increase_income [verification] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:78:5+440
procedure {:timeLimit 40} $42_simple11_test_increase_income$verify() returns ()
{
    // declare local variables
    var $t0: $42_simple11_Employee;
    var $t1: $42_simple11_Employee;
    var $t2: $42_simple11_Employees;
    var $t3: Vec (int);
    var $t4: int;
    var $t5: bv64;
    var $t6: $42_simple11_Employee;
    var $t7: Vec ($42_simple11_Employee);
    var $t8: int;
    var $t9: $Mutation (Vec ($42_simple11_Employee));
    var $t10: $Mutation ($42_simple11_Employees);
    var $t11: $Mutation ($42_simple11_Employee);
    var $t12: int;
    var $t13: $Mutation ($42_simple11_Employee);
    var $t14: bv64;
    var $t15: bv64;
    var $t16: bool;
    var $t17: int;
    var $temp_0'$42_simple11_Employee': $42_simple11_Employee;
    var $temp_0'$42_simple11_Employees': $42_simple11_Employees;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t3 := [99, 104, 97, 111, 115] at /mnt/c/Users/DELL/move-tut/sources/simple11.move:80:19+8
    assume {:print "$at(5,2382,2390)"} true;
    $t3 := ConcatVec(MakeVec4(99, 104, 97, 111), MakeVec1(115));
    assume $IsValid'vec'u8''($t3);

    // $t4 := 21 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:81:18+2
    assume {:print "$at(5,2410,2412)"} true;
    $t4 := 21;
    assume $IsValid'u8'($t4);

    // $t5 := 2000 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:82:21+4
    assume {:print "$at(5,2435,2439)"} true;
    $t5 := 2000bv64;
    assume $IsValid'bv64'($t5);

    // $t6 := pack simple11::Employee($t3, $t4, $t5) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:79:21+99
    assume {:print "$at(5,2352,2451)"} true;
    $t6 := $42_simple11_Employee($t3, $t4, $t5);

    // trace_local[chaos]($t6) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:79:13+5
    assume {:print "$track_local(15,9,0):", $t6} $t6 == $t6;

    // $t7 := vector::empty<simple11::Employee>() on_abort goto L4 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:86:22+15
    assume {:print "$at(5,2514,2529)"} true;
    call $t7 := $1_vector_empty'$42_simple11_Employee'();
    if ($abort_flag) {
        assume {:print "$at(5,2514,2529)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,9):", $t8} $t8 == $t8;
        goto L4;
    }

    // $t9 := borrow_local($t7) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:86:22+15
    $t9 := $Mutation($Local(7), EmptyVec(), $t7);

    // vector::push_back<simple11::Employee>($t9, $t6) on_abort goto L4 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:86:22+15
    call $t9 := $1_vector_push_back'$42_simple11_Employee'($t9, $t6);
    if ($abort_flag) {
        assume {:print "$at(5,2514,2529)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,9):", $t8} $t8 == $t8;
        goto L4;
    }

    // write_back[LocalRoot($t7)@]($t9) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:86:22+15
    $t7 := $Dereference($t9);

    // $t2 := pack simple11::Employees($t7) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:85:25+60
    assume {:print "$at(5,2480,2540)"} true;
    $t2 := $42_simple11_Employees($t7);

    // trace_local[employees]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:85:13+9
    assume {:print "$track_local(15,9,2):", $t2} $t2 == $t2;

    // $t10 := borrow_local($t2) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:89:54+14
    assume {:print "$at(5,2598,2612)"} true;
    $t10 := $Mutation($Local(2), EmptyVec(), $t2);

    // $t1 := simple11::create_employee($t6, $t10) on_abort goto L4 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:89:31+38
    call $t1,$t10 := $42_simple11_create_employee($t6, $t10);
    if ($abort_flag) {
        assume {:print "$at(5,2575,2613)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,9):", $t8} $t8 == $t8;
        goto L4;
    }

    // write_back[LocalRoot($t2)@]($t10) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:89:31+38
    $t2 := $Dereference($t10);

    // trace_local[employees]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:89:31+38
    assume {:print "$track_local(15,9,2):", $t2} $t2 == $t2;

    // trace_local[createdEmployee]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:89:13+15
    assume {:print "$track_local(15,9,1):", $t1} $t1 == $t1;

    // $t11 := borrow_local($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:90:44+20
    assume {:print "$at(5,2659,2679)"} true;
    $t11 := $Mutation($Local(1), EmptyVec(), $t1);

    // $t12 := 200 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:90:66+3
    $t12 := 200;
    assume $IsValid'u64'($t12);

    // $t13 := simple11::increase_income($t11, $t12) on_abort goto L4 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:90:28+42
    call $t13,$t11 := $42_simple11_increase_income($t11, $t12);
    if ($abort_flag) {
        assume {:print "$at(5,2643,2685)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,9):", $t8} $t8 == $t8;
        goto L4;
    }

    // $t14 := get_field<simple11::Employee>.income($t13) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:17+19
    assume {:print "$at(5,2704,2723)"} true;
    $t14 := $Dereference($t13)->$income;

    // write_back[LocalRoot($t1)@]($t11) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:17+19
    $t1 := $Dereference($t11);

    // trace_local[createdEmployee]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:17+19
    assume {:print "$track_local(15,9,1):", $t1} $t1 == $t1;

    // $t15 := 2200 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:40+4
    $t15 := 2200bv64;
    assume $IsValid'bv64'($t15);

    // $t16 := ==($t14, $t15) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:37+2
    $t16 := $IsEqual'bv64'($t14, $t15);

    // if ($t16) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:9+39
    if ($t16) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:9+39
L1:

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:9+39
    assume {:print "$at(5,2696,2735)"} true;
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:46+1
L0:

    // $t17 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:46+1
    assume {:print "$at(5,2733,2734)"} true;
    $t17 := 0;
    assume $IsValid'u64'($t17);

    // trace_abort($t17) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:9+39
    assume {:print "$at(5,2696,2735)"} true;
    assume {:print "$track_abort(15,9):", $t17} $t17 == $t17;

    // $t8 := move($t17) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:9+39
    $t8 := $t17;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:9+39
    goto L4;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:91:9+39
L2:

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:92:5+1
    assume {:print "$at(5,2741,2742)"} true;
L3:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple11.move:92:5+1
    assume {:print "$at(5,2741,2742)"} true;
    return;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple11.move:92:5+1
L4:

    // abort($t8) at /mnt/c/Users/DELL/move-tut/sources/simple11.move:92:5+1
    assume {:print "$at(5,2741,2742)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun silenceCompany::get_company_name [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:5:5+94
procedure {:inline 1} $42_silenceCompany_get_company_name() returns ($ret0: Vec (int))
{
    // declare local variables
    var $t0: Vec (int);
    var $temp_0'vec'u8'': Vec (int);

    // bytecode translation starts here
    // $t0 := [115, 105, 108, 101, 110, 99, 101, 32, 99, 111, 109, 112, 97, 110, 121] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:6:16+18
    assume {:print "$at(6,167,185)"} true;
    $t0 := ConcatVec(ConcatVec(ConcatVec(MakeVec4(115, 105, 108, 101), MakeVec4(110, 99, 101, 32)), MakeVec4(99, 111, 109, 112)), MakeVec3(97, 110, 121));
    assume $IsValid'vec'u8''($t0);

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:6:9+25
    assume {:print "$track_return(16,0,0):", $t0} $t0 == $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:7:5+1
    assume {:print "$at(6,191,192)"} true;
L1:

    // return $t0 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:7:5+1
    assume {:print "$at(6,191,192)"} true;
    $ret0 := $t0;
    return;

}

// fun silenceCompany::get_company_name [verification] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:5:5+94
procedure {:timeLimit 40} $42_silenceCompany_get_company_name$verify() returns ($ret0: Vec (int))
{
    // declare local variables
    var $t0: Vec (int);
    var $temp_0'vec'u8'': Vec (int);

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := [115, 105, 108, 101, 110, 99, 101, 32, 99, 111, 109, 112, 97, 110, 121] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:6:16+18
    assume {:print "$at(6,167,185)"} true;
    $t0 := ConcatVec(ConcatVec(ConcatVec(MakeVec4(115, 105, 108, 101), MakeVec4(110, 99, 101, 32)), MakeVec4(99, 111, 109, 112)), MakeVec3(97, 110, 121));
    assume $IsValid'vec'u8''($t0);

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:6:9+25
    assume {:print "$track_return(16,0,0):", $t0} $t0 == $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:7:5+1
    assume {:print "$at(6,191,192)"} true;
L1:

    // return $t0 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:7:5+1
    assume {:print "$at(6,191,192)"} true;
    $ret0 := $t0;
    return;

}

// struct simple12::Employee at /mnt/c/Users/DELL/move-tut/sources/simple12.move:30:5+119
datatype $42_simple12_Employee {
    $42_simple12_Employee($name: Vec (int), $age: int, $income: int)
}
function {:inline} $Update'$42_simple12_Employee'_name(s: $42_simple12_Employee, x: Vec (int)): $42_simple12_Employee {
    $42_simple12_Employee(x, s->$age, s->$income)
}
function {:inline} $Update'$42_simple12_Employee'_age(s: $42_simple12_Employee, x: int): $42_simple12_Employee {
    $42_simple12_Employee(s->$name, x, s->$income)
}
function {:inline} $Update'$42_simple12_Employee'_income(s: $42_simple12_Employee, x: int): $42_simple12_Employee {
    $42_simple12_Employee(s->$name, s->$age, x)
}
function $IsValid'$42_simple12_Employee'(s: $42_simple12_Employee): bool {
    $IsValid'vec'u8''(s->$name)
      && $IsValid'u8'(s->$age)
      && $IsValid'u64'(s->$income)
}
function {:inline} $IsEqual'$42_simple12_Employee'(s1: $42_simple12_Employee, s2: $42_simple12_Employee): bool {
    $IsEqual'vec'u8''(s1->$name, s2->$name)
    && $IsEqual'u8'(s1->$age, s2->$age)
    && $IsEqual'u64'(s1->$income, s2->$income)}
var $42_simple12_Employee_$memory: $Memory $42_simple12_Employee;

// struct simple12::Employees at /mnt/c/Users/DELL/move-tut/sources/simple12.move:26:5+88
datatype $42_simple12_Employees {
    $42_simple12_Employees($people: Vec ($42_simple12_Employee))
}
function {:inline} $Update'$42_simple12_Employees'_people(s: $42_simple12_Employees, x: Vec ($42_simple12_Employee)): $42_simple12_Employees {
    $42_simple12_Employees(x)
}
function $IsValid'$42_simple12_Employees'(s: $42_simple12_Employees): bool {
    $IsValid'vec'$42_simple12_Employee''(s->$people)
}
function {:inline} $IsEqual'$42_simple12_Employees'(s1: $42_simple12_Employees, s2: $42_simple12_Employees): bool {
    $IsEqual'vec'$42_simple12_Employee''(s1->$people, s2->$people)}
var $42_simple12_Employees_$memory: $Memory $42_simple12_Employees;

// struct simple12::Info at /mnt/c/Users/DELL/move-tut/sources/simple12.move:36:5+110
datatype $42_simple12_Info {
    $42_simple12_Info($company_name: Vec (int), $owns: Vec (bv8))
}
function {:inline} $Update'$42_simple12_Info'_company_name(s: $42_simple12_Info, x: Vec (int)): $42_simple12_Info {
    $42_simple12_Info(x, s->$owns)
}
function {:inline} $Update'$42_simple12_Info'_owns(s: $42_simple12_Info, x: Vec (bv8)): $42_simple12_Info {
    $42_simple12_Info(s->$company_name, x)
}
function $IsValid'$42_simple12_Info'(s: $42_simple12_Info): bool {
    $IsValid'vec'u8''(s->$company_name)
      && $IsValid'vec'bv8''(s->$owns)
}
function {:inline} $IsEqual'$42_simple12_Info'(s1: $42_simple12_Info, s2: $42_simple12_Info): bool {
    $IsEqual'vec'u8''(s1->$company_name, s2->$company_name)
    && $IsEqual'vec'bv8''(s1->$owns, s2->$owns)}
var $42_simple12_Info_$memory: $Memory $42_simple12_Info;

// fun simple12::add_employee [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:61:5+138
procedure {:inline 1} $42_simple12_add_employee(_$t0: $Mutation ($42_simple12_Employees), _$t1: $42_simple12_Employee) returns ($ret0: $Mutation ($42_simple12_Employees))
{
    // declare local variables
    var $t2: $Mutation (Vec ($42_simple12_Employee));
    var $t3: int;
    var $t0: $Mutation ($42_simple12_Employees);
    var $t1: $42_simple12_Employee;
    var $temp_0'$42_simple12_Employee': $42_simple12_Employee;
    var $temp_0'$42_simple12_Employees': $42_simple12_Employees;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[_employees]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:61:5+1
    assume {:print "$at(6,1443,1444)"} true;
    $temp_0'$42_simple12_Employees' := $Dereference($t0);
    assume {:print "$track_local(17,0,0):", $temp_0'$42_simple12_Employees'} $temp_0'$42_simple12_Employees' == $temp_0'$42_simple12_Employees';

    // trace_local[_employee]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:61:5+1
    assume {:print "$track_local(17,0,1):", $t1} $t1 == $t1;

    // $t2 := borrow_field<simple12::Employees>.people($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:62:28+22
    assume {:print "$at(6,1539,1561)"} true;
    $t2 := $ChildMutation($t0, 0, $Dereference($t0)->$people);

    // vector::push_back<simple12::Employee>($t2, $t1) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:62:10+52
    call $t2 := $1_vector_push_back'$42_simple12_Employee'($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(6,1521,1573)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(17,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // write_back[Reference($t0).people (vector<simple12::Employee>)]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:62:10+52
    $t0 := $UpdateMutation($t0, $Update'$42_simple12_Employees'_people($Dereference($t0), $Dereference($t2)));

    // trace_local[_employees]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:62:10+52
    $temp_0'$42_simple12_Employees' := $Dereference($t0);
    assume {:print "$track_local(17,0,0):", $temp_0'$42_simple12_Employees'} $temp_0'$42_simple12_Employees' == $temp_0'$42_simple12_Employees';

    // trace_local[_employees]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:62:62+1
    $temp_0'$42_simple12_Employees' := $Dereference($t0);
    assume {:print "$track_local(17,0,0):", $temp_0'$42_simple12_Employees'} $temp_0'$42_simple12_Employees' == $temp_0'$42_simple12_Employees';

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:63:5+1
    assume {:print "$at(6,1580,1581)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple12.move:63:5+1
    assume {:print "$at(6,1580,1581)"} true;
    $ret0 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:63:5+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:63:5+1
    assume {:print "$at(6,1580,1581)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun simple12::add_employee [verification] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:61:5+138
procedure {:timeLimit 40} $42_simple12_add_employee$verify(_$t0: $Mutation ($42_simple12_Employees), _$t1: $42_simple12_Employee) returns ($ret0: $Mutation ($42_simple12_Employees))
{
    // declare local variables
    var $t2: $Mutation (Vec ($42_simple12_Employee));
    var $t3: int;
    var $t0: $Mutation ($42_simple12_Employees);
    var $t1: $42_simple12_Employee;
    var $temp_0'$42_simple12_Employee': $42_simple12_Employee;
    var $temp_0'$42_simple12_Employees': $42_simple12_Employees;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:61:5+1
    assume {:print "$at(6,1443,1444)"} true;
    assume $IsValid'$42_simple12_Employees'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:61:5+1
    assume $IsValid'$42_simple12_Employee'($t1);

    // trace_local[_employees]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:61:5+1
    $temp_0'$42_simple12_Employees' := $Dereference($t0);
    assume {:print "$track_local(17,0,0):", $temp_0'$42_simple12_Employees'} $temp_0'$42_simple12_Employees' == $temp_0'$42_simple12_Employees';

    // trace_local[_employee]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:61:5+1
    assume {:print "$track_local(17,0,1):", $t1} $t1 == $t1;

    // $t2 := borrow_field<simple12::Employees>.people($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:62:28+22
    assume {:print "$at(6,1539,1561)"} true;
    $t2 := $ChildMutation($t0, 0, $Dereference($t0)->$people);

    // vector::push_back<simple12::Employee>($t2, $t1) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:62:10+52
    call $t2 := $1_vector_push_back'$42_simple12_Employee'($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(6,1521,1573)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(17,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // write_back[Reference($t0).people (vector<simple12::Employee>)]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:62:10+52
    $t0 := $UpdateMutation($t0, $Update'$42_simple12_Employees'_people($Dereference($t0), $Dereference($t2)));

    // trace_local[_employees]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:62:10+52
    $temp_0'$42_simple12_Employees' := $Dereference($t0);
    assume {:print "$track_local(17,0,0):", $temp_0'$42_simple12_Employees'} $temp_0'$42_simple12_Employees' == $temp_0'$42_simple12_Employees';

    // trace_local[_employees]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:62:62+1
    $temp_0'$42_simple12_Employees' := $Dereference($t0);
    assume {:print "$track_local(17,0,0):", $temp_0'$42_simple12_Employees'} $temp_0'$42_simple12_Employees' == $temp_0'$42_simple12_Employees';

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:63:5+1
    assume {:print "$at(6,1580,1581)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple12.move:63:5+1
    assume {:print "$at(6,1580,1581)"} true;
    $ret0 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:63:5+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:63:5+1
    assume {:print "$at(6,1580,1581)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun simple12::create_employee [verification] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:51:5+328
procedure {:timeLimit 40} $42_simple12_create_employee$verify(_$t0: $42_simple12_Employee, _$t1: $Mutation ($42_simple12_Employees)) returns ($ret0: $42_simple12_Employee, $ret1: $Mutation ($42_simple12_Employees))
{
    // declare local variables
    var $t2: $42_simple12_Employee;
    var $t3: Vec (int);
    var $t4: int;
    var $t5: int;
    var $t6: $42_simple12_Employee;
    var $t7: int;
    var $t0: $42_simple12_Employee;
    var $t1: $Mutation ($42_simple12_Employees);
    var $temp_0'$42_simple12_Employee': $42_simple12_Employee;
    var $temp_0'$42_simple12_Employees': $42_simple12_Employees;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t1->l == $Param(1);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:51:5+1
    assume {:print "$at(6,1107,1108)"} true;
    assume $IsValid'$42_simple12_Employee'($t0);

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:51:5+1
    assume $IsValid'$42_simple12_Employees'($Dereference($t1));

    // trace_local[_employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:51:5+1
    assume {:print "$track_local(17,1,0):", $t0} $t0 == $t0;

    // trace_local[_employees]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:51:5+1
    $temp_0'$42_simple12_Employees' := $Dereference($t1);
    assume {:print "$track_local(17,1,1):", $temp_0'$42_simple12_Employees'} $temp_0'$42_simple12_Employees' == $temp_0'$42_simple12_Employees';

    // $t3 := get_field<simple12::Employee>.name($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:53:19+14
    assume {:print "$at(6,1253,1267)"} true;
    $t3 := $t0->$name;

    // $t4 := get_field<simple12::Employee>.age($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:54:18+13
    assume {:print "$at(6,1287,1300)"} true;
    $t4 := $t0->$age;

    // $t5 := get_field<simple12::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:55:21+16
    assume {:print "$at(6,1323,1339)"} true;
    $t5 := $t0->$income;

    // $t6 := pack simple12::Employee($t3, $t4, $t5) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:52:27+128
    assume {:print "$at(6,1223,1351)"} true;
    $t6 := $42_simple12_Employee($t3, $t4, $t5);

    // trace_local[newEmployee]($t6) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:52:13+11
    assume {:print "$track_local(17,1,2):", $t6} $t6 == $t6;

    // simple12::add_employee($t1, $t6) on_abort goto L2 with $t7 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:57:9+37
    assume {:print "$at(6,1362,1399)"} true;
    call $t1 := $42_simple12_add_employee($t1, $t6);
    if ($abort_flag) {
        assume {:print "$at(6,1362,1399)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(17,1):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_return[0]($t6) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:58:9+18
    assume {:print "$at(6,1410,1428)"} true;
    assume {:print "$track_return(17,1,0):", $t6} $t6 == $t6;

    // trace_local[_employees]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:58:9+18
    $temp_0'$42_simple12_Employees' := $Dereference($t1);
    assume {:print "$track_local(17,1,1):", $temp_0'$42_simple12_Employees'} $temp_0'$42_simple12_Employees' == $temp_0'$42_simple12_Employees';

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:59:5+1
    assume {:print "$at(6,1434,1435)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:59:5+1
    assume {:print "$at(6,1434,1435)"} true;
    $ret0 := $t6;
    $ret1 := $t1;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:59:5+1
L2:

    // abort($t7) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:59:5+1
    assume {:print "$at(6,1434,1435)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun simple12::decrease_income [verification] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:70:5+174
procedure {:timeLimit 40} $42_simple12_decrease_income$verify(_$t0: $Mutation ($42_simple12_Employee), _$t1: int) returns ($ret0: $Mutation ($42_simple12_Employee), $ret1: $Mutation ($42_simple12_Employee))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: $Mutation (int);
    var $t6: $Mutation ($42_simple12_Employee);
    var $t0: $Mutation ($42_simple12_Employee);
    var $t1: int;
    var $temp_0'$42_simple12_Employee': $42_simple12_Employee;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:70:5+1
    assume {:print "$at(6,1765,1766)"} true;
    assume $IsValid'$42_simple12_Employee'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:70:5+1
    assume $IsValid'u64'($t1);

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:70:5+1
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_local(17,2,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // trace_local[penality]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:70:5+1
    assume {:print "$track_local(17,2,1):", $t1} $t1 == $t1;

    // $t2 := get_field<simple12::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:71:29+15
    assume {:print "$at(6,1878,1893)"} true;
    $t2 := $Dereference($t0)->$income;

    // $t3 := -($t2, $t1) on_abort goto L2 with $t4 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:71:45+1
    call $t3 := $Sub($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(6,1894,1895)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(17,2):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := borrow_field<simple12::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:71:11+15
    $t5 := $ChildMutation($t0, 2, $Dereference($t0)->$income);

    // write_ref($t5, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:71:11+44
    $t5 := $UpdateMutation($t5, $t3);

    // write_back[Reference($t0).income (u64)]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:71:11+44
    $t0 := $UpdateMutation($t0, $Update'$42_simple12_Employee'_income($Dereference($t0), $Dereference($t5)));

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:71:11+44
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_local(17,2,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:72:11+15
    assume {:print "$at(6,1917,1932)"} true;
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_return(17,2,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:72:11+15
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_local(17,2,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // $t6 := move($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:72:11+15
    $t6 := $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:73:5+1
    assume {:print "$at(6,1938,1939)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:73:5+1
    assume {:print "$at(6,1938,1939)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:73:5+1
L2:

    // abort($t4) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:73:5+1
    assume {:print "$at(6,1938,1939)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun simple12::div_income [verification] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:80:5+168
procedure {:timeLimit 40} $42_simple12_div_income$verify(_$t0: $Mutation ($42_simple12_Employee), _$t1: int) returns ($ret0: $Mutation ($42_simple12_Employee), $ret1: $Mutation ($42_simple12_Employee))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: $Mutation (int);
    var $t6: $Mutation ($42_simple12_Employee);
    var $t0: $Mutation ($42_simple12_Employee);
    var $t1: int;
    var $temp_0'$42_simple12_Employee': $42_simple12_Employee;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:80:5+1
    assume {:print "$at(6,2126,2127)"} true;
    assume $IsValid'$42_simple12_Employee'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:80:5+1
    assume $IsValid'u64'($t1);

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:80:5+1
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_local(17,3,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // trace_local[divisor]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:80:5+1
    assume {:print "$track_local(17,3,1):", $t1} $t1 == $t1;

    // $t2 := get_field<simple12::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:81:29+15
    assume {:print "$at(6,2234,2249)"} true;
    $t2 := $Dereference($t0)->$income;

    // $t3 := /($t2, $t1) on_abort goto L2 with $t4 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:81:45+1
    call $t3 := $Div($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(6,2250,2251)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(17,3):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := borrow_field<simple12::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:81:11+15
    $t5 := $ChildMutation($t0, 2, $Dereference($t0)->$income);

    // write_ref($t5, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:81:11+43
    $t5 := $UpdateMutation($t5, $t3);

    // write_back[Reference($t0).income (u64)]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:81:11+43
    $t0 := $UpdateMutation($t0, $Update'$42_simple12_Employee'_income($Dereference($t0), $Dereference($t5)));

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:81:11+43
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_local(17,3,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:82:11+15
    assume {:print "$at(6,2272,2287)"} true;
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_return(17,3,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:82:11+15
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_local(17,3,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // $t6 := move($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:82:11+15
    $t6 := $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:83:5+1
    assume {:print "$at(6,2293,2294)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:83:5+1
    assume {:print "$at(6,2293,2294)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:83:5+1
L2:

    // abort($t4) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:83:5+1
    assume {:print "$at(6,2293,2294)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun simple12::increase_income [verification] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:65:5+168
procedure {:timeLimit 40} $42_simple12_increase_income$verify(_$t0: $Mutation ($42_simple12_Employee), _$t1: int) returns ($ret0: $Mutation ($42_simple12_Employee), $ret1: $Mutation ($42_simple12_Employee))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: $Mutation (int);
    var $t6: $Mutation ($42_simple12_Employee);
    var $t0: $Mutation ($42_simple12_Employee);
    var $t1: int;
    var $temp_0'$42_simple12_Employee': $42_simple12_Employee;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:65:5+1
    assume {:print "$at(6,1589,1590)"} true;
    assume $IsValid'$42_simple12_Employee'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:65:5+1
    assume $IsValid'u64'($t1);

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:65:5+1
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_local(17,5,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // trace_local[bonus]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:65:5+1
    assume {:print "$track_local(17,5,1):", $t1} $t1 == $t1;

    // $t2 := get_field<simple12::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:66:29+15
    assume {:print "$at(6,1699,1714)"} true;
    $t2 := $Dereference($t0)->$income;

    // $t3 := +($t2, $t1) on_abort goto L2 with $t4 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:66:45+1
    call $t3 := $AddU64($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(6,1715,1716)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(17,5):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := borrow_field<simple12::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:66:11+15
    $t5 := $ChildMutation($t0, 2, $Dereference($t0)->$income);

    // write_ref($t5, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:66:11+41
    $t5 := $UpdateMutation($t5, $t3);

    // write_back[Reference($t0).income (u64)]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:66:11+41
    $t0 := $UpdateMutation($t0, $Update'$42_simple12_Employee'_income($Dereference($t0), $Dereference($t5)));

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:66:11+41
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_local(17,5,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:67:11+15
    assume {:print "$at(6,1735,1750)"} true;
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_return(17,5,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:67:11+15
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_local(17,5,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // $t6 := move($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:67:11+15
    $t6 := $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:68:5+1
    assume {:print "$at(6,1756,1757)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:68:5+1
    assume {:print "$at(6,1756,1757)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:68:5+1
L2:

    // abort($t4) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:68:5+1
    assume {:print "$at(6,1756,1757)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun simple12::is_employee_age_even [verification] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:85:5+242
procedure {:timeLimit 40} $42_simple12_is_employee_age_even$verify(_$t0: $42_simple12_Employee) returns ($ret0: bool)
{
    // declare local variables
    var $t1: bool;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: bool;
    var $t9: bool;
    var $t0: $42_simple12_Employee;
    var $temp_0'$42_simple12_Employee': $42_simple12_Employee;
    var $temp_0'bool': bool;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:85:5+1
    assume {:print "$at(6,2302,2303)"} true;
    assume $IsValid'$42_simple12_Employee'($t0);

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:85:5+1
    assume {:print "$track_local(17,6,0):", $t0} $t0 == $t0;

    // $t2 := get_field<simple12::Employee>.age($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:87:13+12
    assume {:print "$at(6,2405,2417)"} true;
    $t2 := $t0->$age;

    // $t3 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:87:28+1
    $t3 := 2;
    assume $IsValid'u8'($t3);

    // $t4 := %($t2, $t3) on_abort goto L4 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:87:26+1
    call $t4 := $Mod($t2, $t3);
    if ($abort_flag) {
        assume {:print "$at(6,2418,2419)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(17,6):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t6 := 0 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:87:33+1
    $t6 := 0;
    assume $IsValid'u8'($t6);

    // $t7 := ==($t4, $t6) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:87:30+2
    $t7 := $IsEqual'u8'($t4, $t6);

    // if ($t7) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:87:9+112
    if ($t7) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:88:22+4
    assume {:print "$at(6,2452,2456)"} true;
L1:

    // $t8 := true at /mnt/c/Users/DELL/move-tut/sources/simple12.move:88:22+4
    assume {:print "$at(6,2452,2456)"} true;
    $t8 := true;
    assume $IsValid'bool'($t8);

    // $t1 := $t8 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:88:13+6
    $t1 := $t8;

    // trace_local[isEven]($t8) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:88:13+6
    assume {:print "$track_local(17,6,1):", $t8} $t8 == $t8;

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:88:13+13
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:90:22+5
    assume {:print "$at(6,2497,2502)"} true;
L0:

    // $t9 := false at /mnt/c/Users/DELL/move-tut/sources/simple12.move:90:22+5
    assume {:print "$at(6,2497,2502)"} true;
    $t9 := false;
    assume $IsValid'bool'($t9);

    // $t1 := $t9 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:90:13+6
    $t1 := $t9;

    // trace_local[isEven]($t9) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:90:13+6
    assume {:print "$track_local(17,6,1):", $t9} $t9 == $t9;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:92:16+6
    assume {:print "$at(6,2531,2537)"} true;
L2:

    // trace_return[0]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:92:9+13
    assume {:print "$at(6,2524,2537)"} true;
    assume {:print "$track_return(17,6,0):", $t1} $t1 == $t1;

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:93:5+1
    assume {:print "$at(6,2543,2544)"} true;
L3:

    // return $t1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:93:5+1
    assume {:print "$at(6,2543,2544)"} true;
    $ret0 := $t1;
    return;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:93:5+1
L4:

    // abort($t5) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:93:5+1
    assume {:print "$at(6,2543,2544)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun simple12::multiply_income [verification] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:75:6+170
procedure {:timeLimit 40} $42_simple12_multiply_income$verify(_$t0: $Mutation ($42_simple12_Employee), _$t1: int) returns ($ret0: $Mutation ($42_simple12_Employee), $ret1: $Mutation ($42_simple12_Employee))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: $Mutation (int);
    var $t6: $Mutation ($42_simple12_Employee);
    var $t0: $Mutation ($42_simple12_Employee);
    var $t1: int;
    var $temp_0'$42_simple12_Employee': $42_simple12_Employee;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();
    assume $t0->l == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:75:6+1
    assume {:print "$at(6,1948,1949)"} true;
    assume $IsValid'$42_simple12_Employee'($Dereference($t0));

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:75:6+1
    assume $IsValid'u64'($t1);

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:75:6+1
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_local(17,7,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // trace_local[factor]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:75:6+1
    assume {:print "$track_local(17,7,1):", $t1} $t1 == $t1;

    // $t2 := get_field<simple12::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:76:29+15
    assume {:print "$at(6,2059,2074)"} true;
    $t2 := $Dereference($t0)->$income;

    // $t3 := *($t2, $t1) on_abort goto L2 with $t4 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:76:45+1
    call $t3 := $MulU64($t2, $t1);
    if ($abort_flag) {
        assume {:print "$at(6,2075,2076)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(17,7):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := borrow_field<simple12::Employee>.income($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:76:11+15
    $t5 := $ChildMutation($t0, 2, $Dereference($t0)->$income);

    // write_ref($t5, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:76:11+42
    $t5 := $UpdateMutation($t5, $t3);

    // write_back[Reference($t0).income (u64)]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:76:11+42
    $t0 := $UpdateMutation($t0, $Update'$42_simple12_Employee'_income($Dereference($t0), $Dereference($t5)));

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:76:11+42
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_local(17,7,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:77:11+15
    assume {:print "$at(6,2096,2111)"} true;
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_return(17,7,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // trace_local[employee]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:77:11+15
    $temp_0'$42_simple12_Employee' := $Dereference($t0);
    assume {:print "$track_local(17,7,0):", $temp_0'$42_simple12_Employee'} $temp_0'$42_simple12_Employee' == $temp_0'$42_simple12_Employee';

    // $t6 := move($t0) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:77:11+15
    $t6 := $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:78:5+1
    assume {:print "$at(6,2117,2118)"} true;
L1:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:78:5+1
    assume {:print "$at(6,2117,2118)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:78:5+1
L2:

    // abort($t4) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:78:5+1
    assume {:print "$at(6,2117,2118)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun simple12::get_info [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:41:5+259
procedure {:inline 1} $42_simple12_get_info() returns ($ret0: $42_simple12_Info)
{
    // declare local variables
    var $t0: Vec (int);
    var $t1: Vec (int);
    var $t2: int;
    var $t3: Vec (int);
    var $t4: $42_simple12_Info;
    var $temp_0'$42_simple12_Info': $42_simple12_Info;
    var $temp_0'vec'u8'': Vec (int);

    // bytecode translation starts here
    // $t1 := silenceCompany::get_company_name() on_abort goto L2 with $t2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:42:34+44
    assume {:print "$at(6,901,945)"} true;
    call $t1 := $42_silenceCompany_get_company_name();
    if ($abort_flag) {
        assume {:print "$at(6,901,945)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(17,4):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_local[silenceCompanyName]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:42:13+18
    assume {:print "$track_local(17,4,0):", $t1} $t1 == $t1;

    // $t3 := [99, 104, 97, 111, 115, 32, 99, 111, 109, 112, 97, 110, 121] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:43:27+16
    assume {:print "$at(6,999,1015)"} true;
    $t3 := ConcatVec(ConcatVec(ConcatVec(MakeVec4(99, 104, 97, 111), MakeVec4(115, 32, 99, 111)), MakeVec4(109, 112, 97, 110)), MakeVec1(121));
    assume $IsValid'vec'u8''($t3);

    // $t4 := pack simple12::Info($t3, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:42:98+101
    assume {:print "$at(6,965,1066)"} true;
    $t4 := $42_simple12_Info($t3, $t1);

    // trace_return[0]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:46:9+11
    assume {:print "$at(6,1077,1088)"} true;
    assume {:print "$track_return(17,4,0):", $t4} $t4 == $t4;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:47:5+1
    assume {:print "$at(6,1094,1095)"} true;
L1:

    // return $t4 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:47:5+1
    assume {:print "$at(6,1094,1095)"} true;
    $ret0 := $t4;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:47:5+1
L2:

    // abort($t2) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:47:5+1
    assume {:print "$at(6,1094,1095)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun simple12::get_info [verification] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:41:5+259
procedure {:timeLimit 40} $42_simple12_get_info$verify() returns ($ret0: $42_simple12_Info)
{
    // declare local variables
    var $t0: Vec (int);
    var $t1: Vec (int);
    var $t2: int;
    var $t3: Vec (int);
    var $t4: $42_simple12_Info;
    var $temp_0'$42_simple12_Info': $42_simple12_Info;
    var $temp_0'vec'u8'': Vec (int);

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t1 := silenceCompany::get_company_name() on_abort goto L2 with $t2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:42:34+44
    assume {:print "$at(6,901,945)"} true;
    call $t1 := $42_silenceCompany_get_company_name();
    if ($abort_flag) {
        assume {:print "$at(6,901,945)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(17,4):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_local[silenceCompanyName]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:42:13+18
    assume {:print "$track_local(17,4,0):", $t1} $t1 == $t1;

    // $t3 := [99, 104, 97, 111, 115, 32, 99, 111, 109, 112, 97, 110, 121] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:43:27+16
    assume {:print "$at(6,999,1015)"} true;
    $t3 := ConcatVec(ConcatVec(ConcatVec(MakeVec4(99, 104, 97, 111), MakeVec4(115, 32, 99, 111)), MakeVec4(109, 112, 97, 110)), MakeVec1(121));
    assume $IsValid'vec'u8''($t3);

    // $t4 := pack simple12::Info($t3, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:42:98+101
    assume {:print "$at(6,965,1066)"} true;
    $t4 := $42_simple12_Info($t3, $t1);

    // trace_return[0]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:46:9+11
    assume {:print "$at(6,1077,1088)"} true;
    assume {:print "$track_return(17,4,0):", $t4} $t4 == $t4;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:47:5+1
    assume {:print "$at(6,1094,1095)"} true;
L1:

    // return $t4 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:47:5+1
    assume {:print "$at(6,1094,1095)"} true;
    $ret0 := $t4;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:47:5+1
L2:

    // abort($t2) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:47:5+1
    assume {:print "$at(6,1094,1095)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun simple12::test_Friend_func [verification] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:97:5+127
procedure {:timeLimit 40} $42_simple12_test_Friend_func$verify() returns ()
{
    // declare local variables
    var $t0: $42_simple12_Info;
    var $t1: Vec (int);
    var $t2: $42_simple12_Info;
    var $t3: int;
    var $t4: Vec (bv8);
    var $temp_0'$42_simple12_Info': $42_simple12_Info;
    var $temp_0'vec'bv8'': Vec (bv8);

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t2 := simple12::get_info() on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:98:20+10
    assume {:print "$at(6,2619,2629)"} true;
    call $t2 := $42_simple12_get_info();
    if ($abort_flag) {
        assume {:print "$at(6,2619,2629)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(17,8):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_local[comp]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:98:13+4
    assume {:print "$track_local(17,8,0):", $t2} $t2 == $t2;

    // $t4 := get_field<simple12::Info>.owns($t2) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:99:25+9
    assume {:print "$at(6,2656,2665)"} true;
    $t4 := $t2->$owns;

    // trace_local[comp_name]($t4) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:99:13+9
    assume {:print "$track_local(17,8,1):", $t4} $t4 == $t4;

    // debug::print<vector<u8>>($t4) on_abort goto L2 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:100:9+17
    assume {:print "$at(6,2676,2693)"} true;
    call $1_debug_print'vec'u8''($t4);
    if ($abort_flag) {
        assume {:print "$at(6,2676,2693)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(17,8):", $t3} $t3 == $t3;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:101:5+1
    assume {:print "$at(6,2700,2701)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple12.move:101:5+1
    assume {:print "$at(6,2700,2701)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:101:5+1
L2:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:101:5+1
    assume {:print "$at(6,2700,2701)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun simple5::sample_aport_error [verification] at /mnt/c/Users/DELL/move-tut/sources/simple5.move:5:5+198
procedure {:timeLimit 40} $42_simple5_sample_aport_error$verify(_$t0: int) returns ()
{
    // declare local variables
    var $t1: $1_string_String;
    var $t2: int;
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: Vec (int);
    var $t7: $1_string_String;
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple5.move:5:5+1
    assume {:print "$at(12,100,101)"} true;
    assume $IsValid'u64'($t0);

    // trace_local[num]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple5.move:5:5+1
    assume {:print "$track_local(18,0,0):", $t0} $t0 == $t0;

    // $t2 := 10 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:6:20+2
    assume {:print "$at(12,155,157)"} true;
    $t2 := 10;
    assume $IsValid'u64'($t2);

    // $t3 := ==($t0, $t2) at /mnt/c/Users/DELL/move-tut/sources/simple5.move:6:17+2
    $t3 := $IsEqual'u64'($t0, $t2);

    // if ($t3) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:6:10+142
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:6:10+142
L1:

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:6:10+142
    assume {:print "$at(12,145,287)"} true;
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:10:19+3
    assume {:print "$at(12,284,287)"} true;
L0:

    // $t4 := 123 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:10:19+3
    assume {:print "$at(12,284,287)"} true;
    $t4 := 123;
    assume $IsValid'u64'($t4);

    // trace_abort($t4) at /mnt/c/Users/DELL/move-tut/sources/simple5.move:10:13+9
    assume {:print "$at(12,278,287)"} true;
    assume {:print "$track_abort(18,0):", $t4} $t4 == $t4;

    // $t5 := move($t4) at /mnt/c/Users/DELL/move-tut/sources/simple5.move:10:13+9
    $t5 := $t4;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:10:13+9
    goto L4;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:8:25+10
    assume {:print "$at(12,235,245)"} true;
L2:

    // $t6 := [67, 111, 114, 114, 101, 99, 116] at /mnt/c/Users/DELL/move-tut/sources/simple5.move:8:25+10
    assume {:print "$at(12,235,245)"} true;
    $t6 := ConcatVec(MakeVec4(67, 111, 114, 114), MakeVec3(101, 99, 116));
    assume $IsValid'vec'u8''($t6);

    // $t7 := string::utf8($t6) on_abort goto L4 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:8:20+16
    call $t7 := $1_string_utf8($t6);
    if ($abort_flag) {
        assume {:print "$at(12,230,246)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(18,0):", $t5} $t5 == $t5;
        goto L4;
    }

    // debug::print<string::String>($t7) on_abort goto L4 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:8:13+24
    call $1_debug_print'$1_string_String'($t7);
    if ($abort_flag) {
        assume {:print "$at(12,223,247)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(18,0):", $t5} $t5 == $t5;
        goto L4;
    }

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:11:5+1
    assume {:print "$at(12,297,298)"} true;
L3:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple5.move:11:5+1
    assume {:print "$at(12,297,298)"} true;
    return;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:11:5+1
L4:

    // abort($t5) at /mnt/c/Users/DELL/move-tut/sources/simple5.move:11:5+1
    assume {:print "$at(12,297,298)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun simple5::sample_assert_error [verification] at /mnt/c/Users/DELL/move-tut/sources/simple5.move:12:5+113
procedure {:timeLimit 40} $42_simple5_sample_assert_error$verify(_$t0: int) returns ()
{
    // declare local variables
    var $t1: $1_string_String;
    var $t2: int;
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: Vec (int);
    var $t7: $1_string_String;
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple5.move:12:5+1
    assume {:print "$at(12,304,305)"} true;
    assume $IsValid'u64'($t0);

    // trace_local[num]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple5.move:12:5+1
    assume {:print "$track_local(18,1,0):", $t0} $t0 == $t0;

    // $t2 := 10 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:13:25+2
    assume {:print "$at(12,365,367)"} true;
    $t2 := 10;
    assume $IsValid'u64'($t2);

    // $t3 := ==($t0, $t2) at /mnt/c/Users/DELL/move-tut/sources/simple5.move:13:22+2
    $t3 := $IsEqual'u64'($t0, $t2);

    // if ($t3) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:13:10+23
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:13:10+23
L1:

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:13:10+23
    assume {:print "$at(12,350,373)"} true;
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:13:29+3
L0:

    // $t4 := 123 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:13:29+3
    assume {:print "$at(12,369,372)"} true;
    $t4 := 123;
    assume $IsValid'u64'($t4);

    // trace_abort($t4) at /mnt/c/Users/DELL/move-tut/sources/simple5.move:13:10+23
    assume {:print "$at(12,350,373)"} true;
    assume {:print "$track_abort(18,1):", $t4} $t4 == $t4;

    // $t5 := move($t4) at /mnt/c/Users/DELL/move-tut/sources/simple5.move:13:10+23
    $t5 := $t4;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:13:10+23
    goto L4;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:14:22+10
    assume {:print "$at(12,397,407)"} true;
L2:

    // $t6 := [67, 111, 114, 114, 101, 99, 116] at /mnt/c/Users/DELL/move-tut/sources/simple5.move:14:22+10
    assume {:print "$at(12,397,407)"} true;
    $t6 := ConcatVec(MakeVec4(67, 111, 114, 114), MakeVec3(101, 99, 116));
    assume $IsValid'vec'u8''($t6);

    // $t7 := string::utf8($t6) on_abort goto L4 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:14:17+16
    call $t7 := $1_string_utf8($t6);
    if ($abort_flag) {
        assume {:print "$at(12,392,408)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(18,1):", $t5} $t5 == $t5;
        goto L4;
    }

    // debug::print<string::String>($t7) on_abort goto L4 with $t5 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:14:10+24
    call $1_debug_print'$1_string_String'($t7);
    if ($abort_flag) {
        assume {:print "$at(12,385,409)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(18,1):", $t5} $t5 == $t5;
        goto L4;
    }

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:15:5+1
    assume {:print "$at(12,416,417)"} true;
L3:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple5.move:15:5+1
    assume {:print "$at(12,416,417)"} true;
    return;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple5.move:15:5+1
L4:

    // abort($t5) at /mnt/c/Users/DELL/move-tut/sources/simple5.move:15:5+1
    assume {:print "$at(12,416,417)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun simple6::arthemictic_op [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple6.move:10:5+347
procedure {:inline 1} $42_simple6_arthemictic_op(_$t0: int, _$t1: int, _$t2: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t3: int;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: bool;
    var $t10: int;
    var $t11: int;
    var $t12: bool;
    var $t13: int;
    var $t14: int;
    var $t15: bool;
    var $t16: int;
    var $t17: int;
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:10:5+1
    assume {:print "$at(13,204,205)"} true;
    assume {:print "$track_local(19,0,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:10:5+1
    assume {:print "$track_local(19,0,1):", $t1} $t1 == $t1;

    // trace_local[operator]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:10:5+1
    assume {:print "$track_local(19,0,2):", $t2} $t2 == $t2;

    // $t3 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:11:25+3
    assume {:print "$at(13,286,289)"} true;
    $t3 := 1;
    assume $IsValid'u64'($t3);

    // $t4 := ==($t2, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:11:22+2
    $t4 := $IsEqual'u64'($t2, $t3);

    // if ($t4) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:11:9+274
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:12:20+1
    assume {:print "$at(13,312,313)"} true;
L1:

    // $t5 := +($t0, $t1) on_abort goto L9 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:12:22+1
    assume {:print "$at(13,314,315)"} true;
    call $t5 := $AddU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(13,314,315)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(19,0):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_return[0]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:12:13+12
    assume {:print "$track_return(19,0,0):", $t5} $t5 == $t5;

    // $t7 := move($t5) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:12:13+12
    $t7 := $t5;

    // goto L8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:12:13+12
    goto L8;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:13:18+8
    assume {:print "$at(13,337,345)"} true;
L0:

    // $t8 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:13:30+3
    assume {:print "$at(13,349,352)"} true;
    $t8 := 2;
    assume $IsValid'u64'($t8);

    // $t9 := ==($t2, $t8) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:13:27+2
    $t9 := $IsEqual'u64'($t2, $t8);

    // if ($t9) goto L3 else goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:13:14+211
    if ($t9) { goto L3; } else { goto L2; }

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:14:20+1
    assume {:print "$at(13,374,375)"} true;
L3:

    // $t10 := -($t0, $t1) on_abort goto L9 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:14:22+1
    assume {:print "$at(13,376,377)"} true;
    call $t10 := $Sub($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(13,376,377)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(19,0):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_return[0]($t10) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:14:13+12
    assume {:print "$track_return(19,0,0):", $t10} $t10 == $t10;

    // $t7 := move($t10) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:14:13+12
    $t7 := $t10;

    // goto L8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:14:13+12
    goto L8;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:15:18+8
    assume {:print "$at(13,398,406)"} true;
L2:

    // $t11 := 3 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:15:30+3
    assume {:print "$at(13,410,413)"} true;
    $t11 := 3;
    assume $IsValid'u64'($t11);

    // $t12 := ==($t2, $t11) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:15:27+2
    $t12 := $IsEqual'u64'($t2, $t11);

    // if ($t12) goto L5 else goto L4 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:15:14+150
    if ($t12) { goto L5; } else { goto L4; }

    // label L5 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:16:20+1
    assume {:print "$at(13,435,436)"} true;
L5:

    // $t13 := *($t0, $t1) on_abort goto L9 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:16:22+1
    assume {:print "$at(13,437,438)"} true;
    call $t13 := $MulU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(13,437,438)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(19,0):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_return[0]($t13) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:16:13+12
    assume {:print "$track_return(19,0,0):", $t13} $t13 == $t13;

    // $t7 := move($t13) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:16:13+12
    $t7 := $t13;

    // goto L8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:16:13+12
    goto L8;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:17:18+8
    assume {:print "$at(13,460,468)"} true;
L4:

    // $t14 := 4 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:17:30+3
    assume {:print "$at(13,472,475)"} true;
    $t14 := 4;
    assume $IsValid'u64'($t14);

    // $t15 := ==($t2, $t14) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:17:27+2
    $t15 := $IsEqual'u64'($t2, $t14);

    // if ($t15) goto L7 else goto L6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:17:14+88
    if ($t15) { goto L7; } else { goto L6; }

    // label L7 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:18:20+1
    assume {:print "$at(13,497,498)"} true;
L7:

    // $t16 := /($t0, $t1) on_abort goto L9 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:18:22+1
    assume {:print "$at(13,499,500)"} true;
    call $t16 := $Div($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(13,499,500)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(19,0):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_return[0]($t16) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:18:13+12
    assume {:print "$track_return(19,0,0):", $t16} $t16 == $t16;

    // $t7 := move($t16) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:18:13+12
    $t7 := $t16;

    // goto L8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:18:13+12
    goto L8;

    // label L6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:20:20+1
    assume {:print "$at(13,539,540)"} true;
L6:

    // $t17 := %($t0, $t1) on_abort goto L9 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:20:22+1
    assume {:print "$at(13,541,542)"} true;
    call $t17 := $Mod($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(13,541,542)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(19,0):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_return[0]($t17) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:20:13+12
    assume {:print "$track_return(19,0,0):", $t17} $t17 == $t17;

    // $t7 := move($t17) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:20:13+12
    $t7 := $t17;

    // label L8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:21:5+1
    assume {:print "$at(13,550,551)"} true;
L8:

    // return $t7 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:21:5+1
    assume {:print "$at(13,550,551)"} true;
    $ret0 := $t7;
    return;

    // label L9 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:21:5+1
L9:

    // abort($t6) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:21:5+1
    assume {:print "$at(13,550,551)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun simple6::arthemictic_op [verification] at /mnt/c/Users/DELL/move-tut/sources/simple6.move:10:5+347
procedure {:timeLimit 40} $42_simple6_arthemictic_op$verify(_$t0: int, _$t1: int, _$t2: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t3: int;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: bool;
    var $t10: int;
    var $t11: int;
    var $t12: bool;
    var $t13: int;
    var $t14: int;
    var $t15: bool;
    var $t16: int;
    var $t17: int;
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:10:5+1
    assume {:print "$at(13,204,205)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:10:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:10:5+1
    assume $IsValid'u64'($t2);

    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:10:5+1
    assume {:print "$track_local(19,0,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:10:5+1
    assume {:print "$track_local(19,0,1):", $t1} $t1 == $t1;

    // trace_local[operator]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:10:5+1
    assume {:print "$track_local(19,0,2):", $t2} $t2 == $t2;

    // $t3 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:11:25+3
    assume {:print "$at(13,286,289)"} true;
    $t3 := 1;
    assume $IsValid'u64'($t3);

    // $t4 := ==($t2, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:11:22+2
    $t4 := $IsEqual'u64'($t2, $t3);

    // if ($t4) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:11:9+274
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:12:20+1
    assume {:print "$at(13,312,313)"} true;
L1:

    // $t5 := +($t0, $t1) on_abort goto L9 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:12:22+1
    assume {:print "$at(13,314,315)"} true;
    call $t5 := $AddU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(13,314,315)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(19,0):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_return[0]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:12:13+12
    assume {:print "$track_return(19,0,0):", $t5} $t5 == $t5;

    // $t7 := move($t5) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:12:13+12
    $t7 := $t5;

    // goto L8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:12:13+12
    goto L8;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:13:18+8
    assume {:print "$at(13,337,345)"} true;
L0:

    // $t8 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:13:30+3
    assume {:print "$at(13,349,352)"} true;
    $t8 := 2;
    assume $IsValid'u64'($t8);

    // $t9 := ==($t2, $t8) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:13:27+2
    $t9 := $IsEqual'u64'($t2, $t8);

    // if ($t9) goto L3 else goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:13:14+211
    if ($t9) { goto L3; } else { goto L2; }

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:14:20+1
    assume {:print "$at(13,374,375)"} true;
L3:

    // $t10 := -($t0, $t1) on_abort goto L9 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:14:22+1
    assume {:print "$at(13,376,377)"} true;
    call $t10 := $Sub($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(13,376,377)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(19,0):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_return[0]($t10) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:14:13+12
    assume {:print "$track_return(19,0,0):", $t10} $t10 == $t10;

    // $t7 := move($t10) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:14:13+12
    $t7 := $t10;

    // goto L8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:14:13+12
    goto L8;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:15:18+8
    assume {:print "$at(13,398,406)"} true;
L2:

    // $t11 := 3 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:15:30+3
    assume {:print "$at(13,410,413)"} true;
    $t11 := 3;
    assume $IsValid'u64'($t11);

    // $t12 := ==($t2, $t11) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:15:27+2
    $t12 := $IsEqual'u64'($t2, $t11);

    // if ($t12) goto L5 else goto L4 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:15:14+150
    if ($t12) { goto L5; } else { goto L4; }

    // label L5 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:16:20+1
    assume {:print "$at(13,435,436)"} true;
L5:

    // $t13 := *($t0, $t1) on_abort goto L9 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:16:22+1
    assume {:print "$at(13,437,438)"} true;
    call $t13 := $MulU64($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(13,437,438)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(19,0):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_return[0]($t13) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:16:13+12
    assume {:print "$track_return(19,0,0):", $t13} $t13 == $t13;

    // $t7 := move($t13) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:16:13+12
    $t7 := $t13;

    // goto L8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:16:13+12
    goto L8;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:17:18+8
    assume {:print "$at(13,460,468)"} true;
L4:

    // $t14 := 4 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:17:30+3
    assume {:print "$at(13,472,475)"} true;
    $t14 := 4;
    assume $IsValid'u64'($t14);

    // $t15 := ==($t2, $t14) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:17:27+2
    $t15 := $IsEqual'u64'($t2, $t14);

    // if ($t15) goto L7 else goto L6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:17:14+88
    if ($t15) { goto L7; } else { goto L6; }

    // label L7 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:18:20+1
    assume {:print "$at(13,497,498)"} true;
L7:

    // $t16 := /($t0, $t1) on_abort goto L9 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:18:22+1
    assume {:print "$at(13,499,500)"} true;
    call $t16 := $Div($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(13,499,500)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(19,0):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_return[0]($t16) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:18:13+12
    assume {:print "$track_return(19,0,0):", $t16} $t16 == $t16;

    // $t7 := move($t16) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:18:13+12
    $t7 := $t16;

    // goto L8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:18:13+12
    goto L8;

    // label L6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:20:20+1
    assume {:print "$at(13,539,540)"} true;
L6:

    // $t17 := %($t0, $t1) on_abort goto L9 with $t6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:20:22+1
    assume {:print "$at(13,541,542)"} true;
    call $t17 := $Mod($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(13,541,542)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(19,0):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_return[0]($t17) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:20:13+12
    assume {:print "$track_return(19,0,0):", $t17} $t17 == $t17;

    // $t7 := move($t17) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:20:13+12
    $t7 := $t17;

    // label L8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:21:5+1
    assume {:print "$at(13,550,551)"} true;
L8:

    // return $t7 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:21:5+1
    assume {:print "$at(13,550,551)"} true;
    $ret0 := $t7;
    return;

    // label L9 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:21:5+1
L9:

    // abort($t6) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:21:5+1
    assume {:print "$at(13,550,551)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun simple6::equality_op [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple6.move:30:6+306
procedure {:inline 1} $42_simple6_equality_op(_$t0: int, _$t1: int, _$t2: int) returns ($ret0: bool)
{
    // declare local variables
    var $t3: int;
    var $t4: bool;
    var $t5: bool;
    var $t6: bool;
    var $t7: int;
    var $t8: bool;
    var $t9: bool;
    var $t10: int;
    var $t11: bool;
    var $t12: bool;
    var $t13: bool;
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $temp_0'bool': bool;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:30:6+1
    assume {:print "$at(13,716,717)"} true;
    assume {:print "$track_local(19,1,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:30:6+1
    assume {:print "$track_local(19,1,1):", $t1} $t1 == $t1;

    // trace_local[operator]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:30:6+1
    assume {:print "$track_local(19,1,2):", $t2} $t2 == $t2;

    // $t3 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:31:25+6
    assume {:print "$at(13,796,802)"} true;
    $t3 := 1;
    assume $IsValid'u64'($t3);

    // $t4 := ==($t2, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:31:22+2
    $t4 := $IsEqual'u64'($t2, $t3);

    // if ($t4) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:31:9+224
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:32:20+1
    assume {:print "$at(13,825,826)"} true;
L1:

    // $t5 := >($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:32:22+1
    assume {:print "$at(13,827,828)"} true;
    call $t5 := $Gt($t0, $t1);

    // trace_return[0]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:32:13+12
    assume {:print "$track_return(19,1,0):", $t5} $t5 == $t5;

    // $t6 := move($t5) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:32:13+12
    $t6 := $t5;

    // goto L6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:32:13+12
    goto L6;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:33:18+8
    assume {:print "$at(13,849,857)"} true;
L0:

    // $t7 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:33:30+5
    assume {:print "$at(13,861,866)"} true;
    $t7 := 2;
    assume $IsValid'u64'($t7);

    // $t8 := ==($t2, $t7) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:33:27+2
    $t8 := $IsEqual'u64'($t2, $t7);

    // if ($t8) goto L3 else goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:33:14+159
    if ($t8) { goto L3; } else { goto L2; }

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:34:20+1
    assume {:print "$at(13,888,889)"} true;
L3:

    // $t9 := <($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:34:22+1
    assume {:print "$at(13,890,891)"} true;
    call $t9 := $Lt($t0, $t1);

    // trace_return[0]($t9) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:34:13+12
    assume {:print "$track_return(19,1,0):", $t9} $t9 == $t9;

    // $t6 := move($t9) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:34:13+12
    $t6 := $t9;

    // goto L6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:34:13+12
    goto L6;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:35:18+8
    assume {:print "$at(13,912,920)"} true;
L2:

    // $t10 := 3 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:35:30+9
    assume {:print "$at(13,924,933)"} true;
    $t10 := 3;
    assume $IsValid'u64'($t10);

    // $t11 := ==($t2, $t10) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:35:27+2
    $t11 := $IsEqual'u64'($t2, $t10);

    // if ($t11) goto L5 else goto L4 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:35:14+96
    if ($t11) { goto L5; } else { goto L4; }

    // label L5 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:36:20+1
    assume {:print "$at(13,955,956)"} true;
L5:

    // $t12 := >=($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:36:22+2
    assume {:print "$at(13,957,959)"} true;
    call $t12 := $Ge($t0, $t1);

    // trace_return[0]($t12) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:36:13+13
    assume {:print "$track_return(19,1,0):", $t12} $t12 == $t12;

    // $t6 := move($t12) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:36:13+13
    $t6 := $t12;

    // goto L6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:36:13+13
    goto L6;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:38:20+1
    assume {:print "$at(13,998,999)"} true;
L4:

    // $t13 := <=($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:38:22+2
    assume {:print "$at(13,1000,1002)"} true;
    call $t13 := $Le($t0, $t1);

    // trace_return[0]($t13) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:38:13+13
    assume {:print "$track_return(19,1,0):", $t13} $t13 == $t13;

    // $t6 := move($t13) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:38:13+13
    $t6 := $t13;

    // label L6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:40:5+1
    assume {:print "$at(13,1021,1022)"} true;
L6:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:40:5+1
    assume {:print "$at(13,1021,1022)"} true;
    $ret0 := $t6;
    return;

}

// fun simple6::equality_op [verification] at /mnt/c/Users/DELL/move-tut/sources/simple6.move:30:6+306
procedure {:timeLimit 40} $42_simple6_equality_op$verify(_$t0: int, _$t1: int, _$t2: int) returns ($ret0: bool)
{
    // declare local variables
    var $t3: int;
    var $t4: bool;
    var $t5: bool;
    var $t6: bool;
    var $t7: int;
    var $t8: bool;
    var $t9: bool;
    var $t10: int;
    var $t11: bool;
    var $t12: bool;
    var $t13: bool;
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $temp_0'bool': bool;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:30:6+1
    assume {:print "$at(13,716,717)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:30:6+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:30:6+1
    assume $IsValid'u64'($t2);

    // trace_local[a]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:30:6+1
    assume {:print "$track_local(19,1,0):", $t0} $t0 == $t0;

    // trace_local[b]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:30:6+1
    assume {:print "$track_local(19,1,1):", $t1} $t1 == $t1;

    // trace_local[operator]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:30:6+1
    assume {:print "$track_local(19,1,2):", $t2} $t2 == $t2;

    // $t3 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:31:25+6
    assume {:print "$at(13,796,802)"} true;
    $t3 := 1;
    assume $IsValid'u64'($t3);

    // $t4 := ==($t2, $t3) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:31:22+2
    $t4 := $IsEqual'u64'($t2, $t3);

    // if ($t4) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:31:9+224
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:32:20+1
    assume {:print "$at(13,825,826)"} true;
L1:

    // $t5 := >($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:32:22+1
    assume {:print "$at(13,827,828)"} true;
    call $t5 := $Gt($t0, $t1);

    // trace_return[0]($t5) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:32:13+12
    assume {:print "$track_return(19,1,0):", $t5} $t5 == $t5;

    // $t6 := move($t5) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:32:13+12
    $t6 := $t5;

    // goto L6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:32:13+12
    goto L6;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:33:18+8
    assume {:print "$at(13,849,857)"} true;
L0:

    // $t7 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:33:30+5
    assume {:print "$at(13,861,866)"} true;
    $t7 := 2;
    assume $IsValid'u64'($t7);

    // $t8 := ==($t2, $t7) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:33:27+2
    $t8 := $IsEqual'u64'($t2, $t7);

    // if ($t8) goto L3 else goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:33:14+159
    if ($t8) { goto L3; } else { goto L2; }

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:34:20+1
    assume {:print "$at(13,888,889)"} true;
L3:

    // $t9 := <($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:34:22+1
    assume {:print "$at(13,890,891)"} true;
    call $t9 := $Lt($t0, $t1);

    // trace_return[0]($t9) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:34:13+12
    assume {:print "$track_return(19,1,0):", $t9} $t9 == $t9;

    // $t6 := move($t9) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:34:13+12
    $t6 := $t9;

    // goto L6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:34:13+12
    goto L6;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:35:18+8
    assume {:print "$at(13,912,920)"} true;
L2:

    // $t10 := 3 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:35:30+9
    assume {:print "$at(13,924,933)"} true;
    $t10 := 3;
    assume $IsValid'u64'($t10);

    // $t11 := ==($t2, $t10) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:35:27+2
    $t11 := $IsEqual'u64'($t2, $t10);

    // if ($t11) goto L5 else goto L4 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:35:14+96
    if ($t11) { goto L5; } else { goto L4; }

    // label L5 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:36:20+1
    assume {:print "$at(13,955,956)"} true;
L5:

    // $t12 := >=($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:36:22+2
    assume {:print "$at(13,957,959)"} true;
    call $t12 := $Ge($t0, $t1);

    // trace_return[0]($t12) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:36:13+13
    assume {:print "$track_return(19,1,0):", $t12} $t12 == $t12;

    // $t6 := move($t12) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:36:13+13
    $t6 := $t12;

    // goto L6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:36:13+13
    goto L6;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:38:20+1
    assume {:print "$at(13,998,999)"} true;
L4:

    // $t13 := <=($t0, $t1) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:38:22+2
    assume {:print "$at(13,1000,1002)"} true;
    call $t13 := $Le($t0, $t1);

    // trace_return[0]($t13) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:38:13+13
    assume {:print "$track_return(19,1,0):", $t13} $t13 == $t13;

    // $t6 := move($t13) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:38:13+13
    $t6 := $t13;

    // label L6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:40:5+1
    assume {:print "$at(13,1021,1022)"} true;
L6:

    // return $t6 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:40:5+1
    assume {:print "$at(13,1021,1022)"} true;
    $ret0 := $t6;
    return;

}

// fun simple6::test_Op_funtion [verification] at /mnt/c/Users/DELL/move-tut/sources/simple6.move:43:5+322
procedure {:timeLimit 40} $42_simple6_test_Op_funtion$verify() returns ()
{
    // declare local variables
    var $t0: bool;
    var $t1: bool;
    var $t2: bool;
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: bool;
    var $t13: int;
    var $t14: int;
    var $t15: int;
    var $t16: bool;
    var $t17: int;
    var $t18: int;
    var $t19: int;
    var $t20: bool;
    var $temp_0'bool': bool;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t4 := 10 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:44:34+2
    assume {:print "$at(13,1107,1109)"} true;
    $t4 := 10;
    assume $IsValid'u64'($t4);

    // $t5 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:44:38+1
    $t5 := 2;
    assume $IsValid'u64'($t5);

    // $t6 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:44:41+1
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := simple6::equality_op($t4, $t5, $t6) on_abort goto L2 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:44:22+21
    call $t7 := $42_simple6_equality_op($t4, $t5, $t6);
    if ($abort_flag) {
        assume {:print "$at(13,1095,1116)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(19,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[result]($t7) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:44:13+6
    assume {:print "$track_local(19,2,0):", $t7} $t7 == $t7;

    // debug::print<bool>($t7) on_abort goto L2 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:45:9+14
    assume {:print "$at(13,1127,1141)"} true;
    call $1_debug_print'bool'($t7);
    if ($abort_flag) {
        assume {:print "$at(13,1127,1141)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(19,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t9 := 10 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:47:34+2
    assume {:print "$at(13,1179,1181)"} true;
    $t9 := 10;
    assume $IsValid'u64'($t9);

    // $t10 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:47:38+1
    $t10 := 2;
    assume $IsValid'u64'($t10);

    // $t11 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:47:41+1
    $t11 := 2;
    assume $IsValid'u64'($t11);

    // $t12 := simple6::equality_op($t9, $t10, $t11) on_abort goto L2 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:47:22+21
    call $t12 := $42_simple6_equality_op($t9, $t10, $t11);
    if ($abort_flag) {
        assume {:print "$at(13,1167,1188)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(19,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[result#1]($t12) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:47:13+6
    assume {:print "$track_local(19,2,1):", $t12} $t12 == $t12;

    // debug::print<bool>($t12) on_abort goto L2 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:48:9+14
    assume {:print "$at(13,1199,1213)"} true;
    call $1_debug_print'bool'($t12);
    if ($abort_flag) {
        assume {:print "$at(13,1199,1213)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(19,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t13 := 10 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:50:34+2
    assume {:print "$at(13,1251,1253)"} true;
    $t13 := 10;
    assume $IsValid'u64'($t13);

    // $t14 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:50:38+1
    $t14 := 2;
    assume $IsValid'u64'($t14);

    // $t15 := 3 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:50:41+1
    $t15 := 3;
    assume $IsValid'u64'($t15);

    // $t16 := simple6::equality_op($t13, $t14, $t15) on_abort goto L2 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:50:22+21
    call $t16 := $42_simple6_equality_op($t13, $t14, $t15);
    if ($abort_flag) {
        assume {:print "$at(13,1239,1260)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(19,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[result#2]($t16) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:50:13+6
    assume {:print "$track_local(19,2,2):", $t16} $t16 == $t16;

    // debug::print<bool>($t16) on_abort goto L2 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:51:9+14
    assume {:print "$at(13,1271,1285)"} true;
    call $1_debug_print'bool'($t16);
    if ($abort_flag) {
        assume {:print "$at(13,1271,1285)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(19,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t17 := 10 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:53:34+2
    assume {:print "$at(13,1331,1333)"} true;
    $t17 := 10;
    assume $IsValid'u64'($t17);

    // $t18 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:53:38+1
    $t18 := 2;
    assume $IsValid'u64'($t18);

    // $t19 := 4 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:53:41+1
    $t19 := 4;
    assume $IsValid'u64'($t19);

    // $t20 := simple6::equality_op($t17, $t18, $t19) on_abort goto L2 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:53:22+21
    call $t20 := $42_simple6_equality_op($t17, $t18, $t19);
    if ($abort_flag) {
        assume {:print "$at(13,1319,1340)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(19,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[result#3]($t20) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:53:13+6
    assume {:print "$track_local(19,2,3):", $t20} $t20 == $t20;

    // debug::print<bool>($t20) on_abort goto L2 with $t8 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:54:9+14
    assume {:print "$at(13,1351,1365)"} true;
    call $1_debug_print'bool'($t20);
    if ($abort_flag) {
        assume {:print "$at(13,1351,1365)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(19,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:55:5+1
    assume {:print "$at(13,1371,1372)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple6.move:55:5+1
    assume {:print "$at(13,1371,1372)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:55:5+1
L2:

    // abort($t8) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:55:5+1
    assume {:print "$at(13,1371,1372)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun simple6::test_funtion [verification] at /mnt/c/Users/DELL/move-tut/sources/simple6.move:58:5+412
procedure {:timeLimit 40} $42_simple6_test_funtion$verify() returns ()
{
    // declare local variables
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: bv64;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: int;
    var $t13: bv64;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: bv64;
    var $t18: int;
    var $t19: int;
    var $t20: int;
    var $t21: bv64;
    var $t22: int;
    var $t23: int;
    var $t24: int;
    var $t25: bv64;
    var $temp_0'bv64': bv64;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t5 := 10 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:59:37+2
    assume {:print "$at(13,1455,1457)"} true;
    $t5 := 10;
    assume $IsValid'u64'($t5);

    // $t6 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:59:41+1
    $t6 := 2;
    assume $IsValid'u64'($t6);

    // $t7 := 1 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:59:44+1
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // $t8 := simple6::arthemictic_op($t5, $t6, $t7) on_abort goto L2 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:59:22+24
    call $t8 := $42_simple6_arthemictic_op($t5, $t6, $t7);
    if ($abort_flag) {
        assume {:print "$at(13,1440,1464)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(19,3):", $t9} $t9 == $t9;
        goto L2;
    }

    // trace_local[result]($t8) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:59:13+6
    assume {:print "$track_local(19,3,0):", $t8} $t8 == $t8;

    // debug::print<u64>($t8) on_abort goto L2 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:60:9+14
    assume {:print "$at(13,1475,1489)"} true;
    call $1_debug_print'u64'($t8);
    if ($abort_flag) {
        assume {:print "$at(13,1475,1489)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(19,3):", $t9} $t9 == $t9;
        goto L2;
    }

    // $t10 := 10 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:62:37+2
    assume {:print "$at(13,1530,1532)"} true;
    $t10 := 10;
    assume $IsValid'u64'($t10);

    // $t11 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:62:41+1
    $t11 := 2;
    assume $IsValid'u64'($t11);

    // $t12 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:62:44+3
    $t12 := 2;
    assume $IsValid'u64'($t12);

    // $t13 := simple6::arthemictic_op($t10, $t11, $t12) on_abort goto L2 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:62:22+26
    call $t13 := $42_simple6_arthemictic_op($t10, $t11, $t12);
    if ($abort_flag) {
        assume {:print "$at(13,1515,1541)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(19,3):", $t9} $t9 == $t9;
        goto L2;
    }

    // trace_local[result#1]($t13) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:62:13+6
    assume {:print "$track_local(19,3,1):", $t13} $t13 == $t13;

    // debug::print<u64>($t13) on_abort goto L2 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:63:9+14
    assume {:print "$at(13,1552,1566)"} true;
    call $1_debug_print'u64'($t13);
    if ($abort_flag) {
        assume {:print "$at(13,1552,1566)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(19,3):", $t9} $t9 == $t9;
        goto L2;
    }

    // $t14 := 10 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:65:37+2
    assume {:print "$at(13,1607,1609)"} true;
    $t14 := 10;
    assume $IsValid'u64'($t14);

    // $t15 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:65:41+1
    $t15 := 2;
    assume $IsValid'u64'($t15);

    // $t16 := 3 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:65:44+3
    $t16 := 3;
    assume $IsValid'u64'($t16);

    // $t17 := simple6::arthemictic_op($t14, $t15, $t16) on_abort goto L2 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:65:22+26
    call $t17 := $42_simple6_arthemictic_op($t14, $t15, $t16);
    if ($abort_flag) {
        assume {:print "$at(13,1592,1618)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(19,3):", $t9} $t9 == $t9;
        goto L2;
    }

    // trace_local[result#2]($t17) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:65:13+6
    assume {:print "$track_local(19,3,2):", $t17} $t17 == $t17;

    // debug::print<u64>($t17) on_abort goto L2 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:66:9+14
    assume {:print "$at(13,1629,1643)"} true;
    call $1_debug_print'u64'($t17);
    if ($abort_flag) {
        assume {:print "$at(13,1629,1643)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(19,3):", $t9} $t9 == $t9;
        goto L2;
    }

    // $t18 := 10 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:68:37+2
    assume {:print "$at(13,1692,1694)"} true;
    $t18 := 10;
    assume $IsValid'u64'($t18);

    // $t19 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:68:41+1
    $t19 := 2;
    assume $IsValid'u64'($t19);

    // $t20 := 4 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:68:44+3
    $t20 := 4;
    assume $IsValid'u64'($t20);

    // $t21 := simple6::arthemictic_op($t18, $t19, $t20) on_abort goto L2 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:68:22+26
    call $t21 := $42_simple6_arthemictic_op($t18, $t19, $t20);
    if ($abort_flag) {
        assume {:print "$at(13,1677,1703)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(19,3):", $t9} $t9 == $t9;
        goto L2;
    }

    // trace_local[result#3]($t21) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:68:13+6
    assume {:print "$track_local(19,3,3):", $t21} $t21 == $t21;

    // debug::print<u64>($t21) on_abort goto L2 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:69:9+14
    assume {:print "$at(13,1714,1728)"} true;
    call $1_debug_print'u64'($t21);
    if ($abort_flag) {
        assume {:print "$at(13,1714,1728)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(19,3):", $t9} $t9 == $t9;
        goto L2;
    }

    // $t22 := 11 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:71:37+2
    assume {:print "$at(13,1769,1771)"} true;
    $t22 := 11;
    assume $IsValid'u64'($t22);

    // $t23 := 2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:71:41+1
    $t23 := 2;
    assume $IsValid'u64'($t23);

    // $t24 := 7 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:71:44+1
    $t24 := 7;
    assume $IsValid'u64'($t24);

    // $t25 := simple6::arthemictic_op($t22, $t23, $t24) on_abort goto L2 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:71:22+24
    call $t25 := $42_simple6_arthemictic_op($t22, $t23, $t24);
    if ($abort_flag) {
        assume {:print "$at(13,1754,1778)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(19,3):", $t9} $t9 == $t9;
        goto L2;
    }

    // trace_local[result#4]($t25) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:71:13+6
    assume {:print "$track_local(19,3,4):", $t25} $t25 == $t25;

    // debug::print<u64>($t25) on_abort goto L2 with $t9 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:72:9+14
    assume {:print "$at(13,1789,1803)"} true;
    call $1_debug_print'u64'($t25);
    if ($abort_flag) {
        assume {:print "$at(13,1789,1803)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(19,3):", $t9} $t9 == $t9;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:73:5+1
    assume {:print "$at(13,1809,1810)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple6.move:73:5+1
    assume {:print "$at(13,1809,1810)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple6.move:73:5+1
L2:

    // abort($t9) at /mnt/c/Users/DELL/move-tut/sources/simple6.move:73:5+1
    assume {:print "$at(13,1809,1810)"} true;
    $abort_code := $t9;
    $abort_flag := true;
    return;

}

// struct simple9::Person at /mnt/c/Users/DELL/move-tut/sources/simple9.move:3:5+50
datatype $42_simple9_Person {
    $42_simple9_Person($age: int)
}
function {:inline} $Update'$42_simple9_Person'_age(s: $42_simple9_Person, x: int): $42_simple9_Person {
    $42_simple9_Person(x)
}
function $IsValid'$42_simple9_Person'(s: $42_simple9_Person): bool {
    $IsValid'u64'(s->$age)
}
function {:inline} $IsEqual'$42_simple9_Person'(s1: $42_simple9_Person, s2: $42_simple9_Person): bool {
    s1 == s2
}

// fun simple9::set_age [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple9.move:7:5+120
procedure {:inline 1} $42_simple9_set_age(_$t0: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t1: $42_simple9_Person;
    var $t2: $42_simple9_Person;
    var $t3: int;
    var $t0: int;
    var $temp_0'$42_simple9_Person': $42_simple9_Person;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[new_age]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:7:5+1
    assume {:print "$at(16,118,119)"} true;
    assume {:print "$track_local(20,0,0):", $t0} $t0 == $t0;

    // $t2 := pack simple9::Person($t0) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:8:22+23
    assume {:print "$at(16,180,203)"} true;
    $t2 := $42_simple9_Person($t0);

    // trace_local[person]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:8:13+6
    assume {:print "$track_local(20,0,1):", $t2} $t2 == $t2;

    // $t3 := get_field<simple9::Person>.age($t2) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:9:16+10
    assume {:print "$at(16,221,231)"} true;
    $t3 := $t2->$age;

    // trace_return[0]($t3) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:9:9+17
    assume {:print "$track_return(20,0,0):", $t3} $t3 == $t3;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:10:5+1
    assume {:print "$at(16,237,238)"} true;
L1:

    // return $t3 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:10:5+1
    assume {:print "$at(16,237,238)"} true;
    $ret0 := $t3;
    return;

}

// fun simple9::set_age [verification] at /mnt/c/Users/DELL/move-tut/sources/simple9.move:7:5+120
procedure {:timeLimit 40} $42_simple9_set_age$verify(_$t0: int) returns ($ret0: bv64)
{
    // declare local variables
    var $t1: $42_simple9_Person;
    var $t2: $42_simple9_Person;
    var $t3: int;
    var $t0: int;
    var $temp_0'$42_simple9_Person': $42_simple9_Person;
    var $temp_0'u64': int;
    var $temp_0'bv64': bv64;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:7:5+1
    assume {:print "$at(16,118,119)"} true;
    assume $IsValid'u64'($t0);

    // trace_local[new_age]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:7:5+1
    assume {:print "$track_local(20,0,0):", $t0} $t0 == $t0;

    // $t2 := pack simple9::Person($t0) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:8:22+23
    assume {:print "$at(16,180,203)"} true;
    $t2 := $42_simple9_Person($t0);

    // trace_local[person]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:8:13+6
    assume {:print "$track_local(20,0,1):", $t2} $t2 == $t2;

    // $t3 := get_field<simple9::Person>.age($t2) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:9:16+10
    assume {:print "$at(16,221,231)"} true;
    $t3 := $t2->$age;

    // trace_return[0]($t3) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:9:9+17
    assume {:print "$track_return(20,0,0):", $t3} $t3 == $t3;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:10:5+1
    assume {:print "$at(16,237,238)"} true;
L1:

    // return $t3 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:10:5+1
    assume {:print "$at(16,237,238)"} true;
    $ret0 := $t3;
    return;

}

// fun simple9::test_set_age [verification] at /mnt/c/Users/DELL/move-tut/sources/simple9.move:13:5+120
procedure {:timeLimit 40} $42_simple9_test_set_age$verify() returns ()
{
    // declare local variables
    var $t0: int;
    var $t1: int;
    var $t2: bv64;
    var $t3: int;
    var $t4: bv64;
    var $t5: bool;
    var $t6: int;
    var $temp_0'bv64': bv64;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t1 := 100 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:14:28+3
    assume {:print "$at(16,311,314)"} true;
    $t1 := 100;
    assume $IsValid'u64'($t1);

    // $t2 := simple9::set_age($t1) on_abort goto L4 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:14:20+12
    call $t2 := $42_simple9_set_age($t1);
    if ($abort_flag) {
        assume {:print "$at(16,303,315)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(20,1):", $t3} $t3 == $t3;
        goto L4;
    }

    // trace_local[age]($t2) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:14:14+3
    assume {:print "$track_local(20,1,0):", $t2} $t2 == $t2;

    // $t4 := 100 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:15:25+3
    assume {:print "$at(16,342,345)"} true;
    $t4 := 100bv64;
    assume $IsValid'bv64'($t4);

    // $t5 := ==($t2, $t4) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:15:22+2
    $t5 := $IsEqual'bv64'($t2, $t4);

    // if ($t5) goto L1 else goto L0 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:15:10+24
    if ($t5) { goto L1; } else { goto L0; }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:15:10+24
L1:

    // goto L2 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:15:10+24
    assume {:print "$at(16,327,351)"} true;
    goto L2;

    // label L0 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:15:30+3
L0:

    // $t6 := 100 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:15:30+3
    assume {:print "$at(16,347,350)"} true;
    $t6 := 100;
    assume $IsValid'u64'($t6);

    // trace_abort($t6) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:15:10+24
    assume {:print "$at(16,327,351)"} true;
    assume {:print "$track_abort(20,1):", $t6} $t6 == $t6;

    // $t3 := move($t6) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:15:10+24
    $t3 := $t6;

    // goto L4 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:15:10+24
    goto L4;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:16:16+4
    assume {:print "$at(16,369,373)"} true;
L2:

    // debug::print<u64>($t2) on_abort goto L4 with $t3 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:16:10+11
    assume {:print "$at(16,363,374)"} true;
    call $1_debug_print'u64'($t2);
    if ($abort_flag) {
        assume {:print "$at(16,363,374)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(20,1):", $t3} $t3 == $t3;
        goto L4;
    }

    // label L3 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:17:5+1
    assume {:print "$at(16,381,382)"} true;
L3:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple9.move:17:5+1
    assume {:print "$at(16,381,382)"} true;
    return;

    // label L4 at /mnt/c/Users/DELL/move-tut/sources/simple9.move:17:5+1
L4:

    // abort($t3) at /mnt/c/Users/DELL/move-tut/sources/simple9.move:17:5+1
    assume {:print "$at(16,381,382)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun one::get_prices [verification] at /mnt/c/Users/DELL/move-tut/sources/simple3.move:14:9+64
procedure {:timeLimit 40} $42_one_get_prices$verify() returns ($ret0: int)
{
    // declare local variables
    var $t0: int;
    var $temp_0'u64': int;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := 90 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:15:20+2
    assume {:print "$at(10,278,280)"} true;
    $t0 := 90;
    assume $IsValid'u64'($t0);

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple3.move:15:13+9
    assume {:print "$track_return(21,0,0):", $t0} $t0 == $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:16:9+1
    assume {:print "$at(10,290,291)"} true;
L1:

    // return $t0 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:16:9+1
    assume {:print "$at(10,290,291)"} true;
    $ret0 := $t0;
    return;

}

// fun one::get_value [baseline] at /mnt/c/Users/DELL/move-tut/sources/simple3.move:9:9+72
procedure {:inline 1} $42_one_get_value() returns ($ret0: bv64)
{
    // declare local variables
    var $t0: int;
    var $temp_0'bv64': bv64;

    // bytecode translation starts here
    // $t0 := 100 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:10:20+3
    assume {:print "$at(10,184,187)"} true;
    $t0 := 100;
    assume $IsValid'u64'($t0);

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple3.move:10:13+10
    assume {:print "$track_return(21,1,0):", $t0} $t0 == $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:11:9+1
    assume {:print "$at(10,197,198)"} true;
L1:

    // return $t0 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:11:9+1
    assume {:print "$at(10,197,198)"} true;
    $ret0 := $t0;
    return;

}

// fun one::get_value [verification] at /mnt/c/Users/DELL/move-tut/sources/simple3.move:9:9+72
procedure {:timeLimit 40} $42_one_get_value$verify() returns ($ret0: bv64)
{
    // declare local variables
    var $t0: int;
    var $temp_0'bv64': bv64;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := 100 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:10:20+3
    assume {:print "$at(10,184,187)"} true;
    $t0 := 100;
    assume $IsValid'u64'($t0);

    // trace_return[0]($t0) at /mnt/c/Users/DELL/move-tut/sources/simple3.move:10:13+10
    assume {:print "$track_return(21,1,0):", $t0} $t0 == $t0;

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:11:9+1
    assume {:print "$at(10,197,198)"} true;
L1:

    // return $t0 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:11:9+1
    assume {:print "$at(10,197,198)"} true;
    $ret0 := $t0;
    return;

}

// fun three::test_function [verification] at /mnt/c/Users/DELL/move-tut/sources/simple3.move:37:9+109
procedure {:timeLimit 40} $42_three_test_function$verify() returns ()
{
    // declare local variables
    var $t0: int;
    var $t1: bv64;
    var $t2: int;
    var $temp_0'bv64': bv64;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t1 := one::get_value() on_abort goto L2 with $t2 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:38:26+11
    assume {:print "$at(10,722,733)"} true;
    call $t1 := $42_one_get_value();
    if ($abort_flag) {
        assume {:print "$at(10,722,733)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(22,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_local[result]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple3.move:38:17+6
    assume {:print "$track_local(22,0,0):", $t1} $t1 == $t1;

    // debug::print<u64>($t1) on_abort goto L2 with $t2 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:39:13+21
    assume {:print "$at(10,748,769)"} true;
    call $1_debug_print'u64'($t1);
    if ($abort_flag) {
        assume {:print "$at(10,748,769)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(22,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:41:9+1
    assume {:print "$at(10,782,783)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple3.move:41:9+1
    assume {:print "$at(10,782,783)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:41:9+1
L2:

    // abort($t2) at /mnt/c/Users/DELL/move-tut/sources/simple3.move:41:9+1
    assume {:print "$at(10,782,783)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun two::test_function [verification] at /mnt/c/Users/DELL/move-tut/sources/simple3.move:24:9+109
procedure {:timeLimit 40} $42_two_test_function$verify() returns ()
{
    // declare local variables
    var $t0: int;
    var $t1: bv64;
    var $t2: int;
    var $temp_0'bv64': bv64;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t1 := one::get_value() on_abort goto L2 with $t2 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:25:26+11
    assume {:print "$at(10,467,478)"} true;
    call $t1 := $42_one_get_value();
    if ($abort_flag) {
        assume {:print "$at(10,467,478)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(23,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_local[result]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple3.move:25:17+6
    assume {:print "$track_local(23,0,0):", $t1} $t1 == $t1;

    // debug::print<u64>($t1) on_abort goto L2 with $t2 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:26:13+21
    assume {:print "$at(10,493,514)"} true;
    call $1_debug_print'u64'($t1);
    if ($abort_flag) {
        assume {:print "$at(10,493,514)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(23,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:28:9+1
    assume {:print "$at(10,527,528)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple3.move:28:9+1
    assume {:print "$at(10,527,528)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple3.move:28:9+1
L2:

    // abort($t2) at /mnt/c/Users/DELL/move-tut/sources/simple3.move:28:9+1
    assume {:print "$at(10,527,528)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun do_stuff::do_stuff [verification] at /mnt/c/Users/DELL/move-tut/sources/simple12.move:13:5+95
procedure {:timeLimit 40} $ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_do_stuff_do_stuff$verify() returns ()
{
    // declare local variables
    var $t0: $42_simple12_Info;
    var $t1: $42_simple12_Info;
    var $t2: int;
    var $temp_0'$42_simple12_Info': $42_simple12_Info;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t1 := simple12::get_info() on_abort goto L2 with $t2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:14:20+20
    assume {:print "$at(6,300,320)"} true;
    call $t1 := $42_simple12_get_info();
    if ($abort_flag) {
        assume {:print "$at(6,300,320)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(24,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_local[info]($t1) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:14:13+4
    assume {:print "$track_local(24,0,0):", $t1} $t1 == $t1;

    // debug::print<simple12::Info>($t1) on_abort goto L2 with $t2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:15:9+19
    assume {:print "$at(6,331,350)"} true;
    call $1_debug_print'$42_simple12_Info'($t1);
    if ($abort_flag) {
        assume {:print "$at(6,331,350)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(24,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // label L1 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:16:5+1
    assume {:print "$at(6,357,358)"} true;
L1:

    // return () at /mnt/c/Users/DELL/move-tut/sources/simple12.move:16:5+1
    assume {:print "$at(6,357,358)"} true;
    return;

    // label L2 at /mnt/c/Users/DELL/move-tut/sources/simple12.move:16:5+1
L2:

    // abort($t2) at /mnt/c/Users/DELL/move-tut/sources/simple12.move:16:5+1
    assume {:print "$at(6,357,358)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}
