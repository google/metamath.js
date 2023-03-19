include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "co.mm"
include "cmpt2.mm"
include "cvv.mm"
include "cfv.mm"
include "wceq.mm"
include "cfn.mm"
include "matrcl.mm"
include "simpld.mm"
include "mpt2exga.mm"
include "syl2anc.mm"
include "oveq.mm"
include "mpt2eq3dv.mm"
include "submafval.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem submaval0
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vl: setvar l
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assume submafval.a: |- A = ( N Mat R )
  assume submafval.q: |- Q = ( N subMat R )
  assume submafval.b: |- B = ( Base ` A )

  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N l
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R l
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M l
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint j m
  disjoint j n
  disjoint j r
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint l m
  disjoint l n
  disjoint l r
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint M m
  assert |- ( M e. B -> ( Q ` M ) = ( k e. N , l e. N |-> ( i e. ( N \ { k } ) , j e. ( N \ { l } ) |-> ( i M j ) ) ) )

  proof
    cM
    cB
    wcel
    #
    vk
    vl
    cN
    cN
    vi
    vj
    cN
    vk
    cv
    csn
    cdif
    #
    cN
    vl
    cv
    csn
    cdif
    #
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    cmpt2
    #
    cmpt2
    #
    cvv
    wcel
    #
    cM
    cQ
    cfv
    @7
    wceq
    @0
    cN
    cfn
    wcel
    #
    @9
    @8
    @0
    @9
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    submafval.a
    submafval.b
    matrcl
    simpld
    #
    @10
    vk
    vl
    cN
    cN
    @6
    cfn
    cfn
    mpt2exga
    syl2anc
    vm
    cM
    vk
    vl
    cN
    cN
    vi
    vj
    @1
    @2
    @3
    @4
    vm
    cv
    #
    co
    #
    cmpt2
    #
    cmpt2
    @7
    cB
    cvv
    cQ
    @11
    cM
    wceq
    #
    vk
    vl
    cN
    cN
    @13
    @6
    @14
    vi
    vj
    @1
    @2
    @12
    @5
    @3
    @4
    @11
    cM
    oveq
    mpt2eq3dv
    mpt2eq3dv
    cA
    cB
    cQ
    cR
    vi
    vj
    vk
    vm
    cN
    vl
    submafval.a
    submafval.q
    submafval.b
    submafval
    fvmptg
    mpdan
end
