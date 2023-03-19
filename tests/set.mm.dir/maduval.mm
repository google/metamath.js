include "wcel.mm"
include "weq.mm"
include "cif.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cfv.mm"
include "cvv.mm"
include "wceq.mm"
include "cfn.mm"
include "matrcl.mm"
include "simpld.mm"
include "mpt2exga.mm"
include "syl2anc.mm"
include "w3a.mm"
include "oveq.mm"
include "ifeq2d.mm"
include "mpt2eq3dv.mm"
include "3ad2ant1.mm"
include "fveq2d.mm"
include "mpt2eq3dva.mm"
include "madufval.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem maduval
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cJ: class J
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vl: setvar l
  let vn: setvar n
  let vr: setvar r
  let vm: setvar m
  assume madufval.a: |- A = ( N Mat R )
  assume madufval.d: |- D = ( N maDet R )
  assume madufval.j: |- J = ( N maAdju R )
  assume madufval.b: |- B = ( Base ` A )
  assume madufval.o: |- .1. = ( 1r ` R )
  assume madufval.z: |- .0. = ( 0g ` R )

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
  disjoint N n
  disjoint N r
  disjoint N m
  disjoint n r
  disjoint m n
  disjoint i n
  disjoint j n
  disjoint k n
  disjoint l n
  disjoint m r
  disjoint i r
  disjoint j r
  disjoint k r
  disjoint l r
  disjoint i m
  disjoint j m
  disjoint k m
  disjoint l m
  disjoint R n
  disjoint R r
  disjoint R m
  disjoint B m
  disjoint M m
  disjoint D m
  disjoint .1. m
  disjoint .0. m
  assert |- ( M e. B -> ( J ` M ) = ( i e. N , j e. N |-> ( D ` ( k e. N , l e. N |-> if ( k = j , if ( l = i , .1. , .0. ) , ( k M l ) ) ) ) ) )

  proof
    cM
    cB
    wcel
    #
    vi
    vj
    cN
    cN
    vk
    vl
    cN
    cN
    vk
    vj
    weq
    #
    vl
    vi
    weq
    c.1
    c.0
    cif
    #
    vk
    cv
    #
    vl
    cv
    #
    cM
    co
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    cmpt2
    #
    cvv
    wcel
    #
    cM
    cJ
    cfv
    @9
    wceq
    @0
    cN
    cfn
    wcel
    #
    @11
    @10
    @0
    @11
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    madufval.a
    madufval.b
    matrcl
    simpld
    #
    @12
    vi
    vj
    cN
    cN
    @8
    cfn
    cfn
    mpt2exga
    syl2anc
    vm
    cM
    vi
    vj
    cN
    cN
    vk
    vl
    cN
    cN
    @1
    @2
    @3
    @4
    vm
    cv
    #
    co
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    cmpt2
    @9
    cB
    cvv
    cJ
    @13
    cM
    wceq
    #
    vi
    vj
    cN
    cN
    @17
    @8
    @18
    vi
    cv
    cN
    wcel
    #
    vj
    cv
    cN
    wcel
    #
    w3a
    @16
    @7
    cD
    @18
    @19
    @16
    @7
    wceq
    @20
    @18
    vk
    vl
    cN
    cN
    @15
    @6
    @18
    @1
    @14
    @5
    @2
    @3
    @4
    @13
    cM
    oveq
    ifeq2d
    mpt2eq3dv
    3ad2ant1
    fveq2d
    mpt2eq3dva
    cA
    cB
    cD
    cR
    c.1
    vi
    vj
    vk
    vm
    cJ
    cN
    c.0
    vl
    madufval.a
    madufval.d
    madufval.j
    madufval.b
    madufval.o
    madufval.z
    madufval
    fvmptg
    mpdan
end
