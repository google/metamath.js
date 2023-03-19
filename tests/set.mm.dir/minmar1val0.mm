include "wcel.mm"
include "weq.mm"
include "cif.mm"
include "cv.mm"
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
include "ifeq2d.mm"
include "mpt2eq3dv.mm"
include "minmar1fval.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem minmar1val0
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vl: setvar l
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assume minmar1fval.a: |- A = ( N Mat R )
  assume minmar1fval.b: |- B = ( Base ` A )
  assume minmar1fval.q: |- Q = ( N minMatR1 R )
  assume minmar1fval.o: |- .1. = ( 1r ` R )
  assume minmar1fval.z: |- .0. = ( 0g ` R )

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
  disjoint .1. n
  disjoint .1. r
  disjoint .0. n
  disjoint .0. r
  disjoint M m
  disjoint .1. m
  disjoint .0. m
  assert |- ( M e. B -> ( Q ` M ) = ( k e. N , l e. N |-> ( i e. N , j e. N |-> if ( i = k , if ( j = l , .1. , .0. ) , ( i M j ) ) ) ) )

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
    cN
    vi
    vk
    weq
    #
    vj
    vl
    weq
    c.1
    c.0
    cif
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
    cif
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
    @8
    wceq
    @0
    cN
    cfn
    wcel
    #
    @10
    @9
    @0
    @10
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    minmar1fval.a
    minmar1fval.b
    matrcl
    simpld
    #
    @11
    vk
    vl
    cN
    cN
    @7
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
    cmpt2
    @8
    cB
    cvv
    cQ
    @12
    cM
    wceq
    #
    vk
    vl
    cN
    cN
    @15
    @7
    @16
    vi
    vj
    cN
    cN
    @14
    @6
    @16
    @1
    @13
    @5
    @2
    @3
    @4
    @12
    cM
    oveq
    ifeq2d
    mpt2eq3dv
    mpt2eq3dv
    cA
    cB
    cQ
    cR
    c.1
    vi
    vj
    vk
    vm
    cN
    c.0
    vl
    minmar1fval.a
    minmar1fval.b
    minmar1fval.q
    minmar1fval.o
    minmar1fval.z
    minmar1fval
    fvmptg
    mpdan
end
