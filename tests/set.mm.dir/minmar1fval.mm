include "cminmar1.mm"
include "co.mm"
include "weq.mm"
include "cif.mm"
include "cv.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cmat.mm"
include "cbs.mm"
include "cfv.mm"
include "cur.mm"
include "c0g.mm"
include "oveq12.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "simpl.mm"
include "fveq2.mm"
include "ifeq12d.mm"
include "ifeq1d.mm"
include "adantl.mm"
include "mpt2eq123dv.mm"
include "mpteq12dv.mm"
include "df-minmar1.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "wn.mm"
include "c0.mm"
include "mpt2ndm0.mm"
include "mpt0.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "matbas0pc.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem minmar1fval
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cN: class N
  let c.0: class .0.
  let vl: setvar l
  let vn: setvar n
  let vr: setvar r
  assume minmar1fval.a: |- A = ( N Mat R )
  assume minmar1fval.b: |- B = ( Base ` A )
  assume minmar1fval.q: |- Q = ( N minMatR1 R )
  assume minmar1fval.o: |- .1. = ( 1r ` R )
  assume minmar1fval.z: |- .0. = ( 0g ` R )

  disjoint B m
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N l
  disjoint N m
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R l
  disjoint R m
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint N n
  disjoint N r
  disjoint i n
  disjoint i r
  disjoint j n
  disjoint j r
  disjoint k n
  disjoint k r
  disjoint l n
  disjoint l r
  disjoint R n
  disjoint R r
  disjoint .1. n
  disjoint .1. r
  disjoint .0. n
  disjoint .0. r
  assert |- Q = ( m e. B |-> ( k e. N , l e. N |-> ( i e. N , j e. N |-> if ( i = k , if ( j = l , .1. , .0. ) , ( i m j ) ) ) ) )

  proof
    cQ
    cN
    cR
    cminmar1
    co
    #
    vm
    cB
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
    #
    c.1
    c.0
    cif
    #
    vi
    cv
    vj
    cv
    vm
    cv
    co
    #
    cif
    #
    cmpt2
    #
    cmpt2
    #
    cmpt
    #
    minmar1fval.q
    cN
    cvv
    wcel
    cR
    cvv
    wcel
    wa
    #
    @0
    @8
    wceq
    vn
    vr
    cN
    cR
    cvv
    cvv
    vm
    vn
    cv
    #
    vr
    cv
    #
    cmat
    co
    #
    cbs
    cfv
    #
    vk
    vl
    @10
    @10
    vi
    vj
    @10
    @10
    @1
    @2
    @11
    cur
    cfv
    #
    @11
    c0g
    cfv
    #
    cif
    #
    @4
    cif
    #
    cmpt2
    #
    cmpt2
    #
    cmpt
    #
    @8
    cminmar1
    @10
    cN
    wceq
    #
    @11
    cR
    wceq
    #
    wa
    #
    vm
    @13
    @19
    cB
    @7
    @23
    @13
    cA
    cbs
    cfv
    #
    cB
    @23
    @12
    cA
    cbs
    @23
    @12
    cN
    cR
    cmat
    co
    #
    cA
    @10
    cN
    @11
    cR
    cmat
    oveq12
    minmar1fval.a
    syl6eqr
    fveq2d
    minmar1fval.b
    syl6eqr
    @23
    vk
    vl
    @10
    @10
    @18
    cN
    cN
    @6
    @21
    @22
    simpl
    #
    @26
    @23
    vi
    vj
    @10
    @10
    @17
    cN
    cN
    @5
    @26
    @26
    @22
    @17
    @5
    wceq
    @21
    @22
    @1
    @16
    @3
    @4
    @22
    @2
    @14
    c.1
    @15
    c.0
    @22
    @14
    cR
    cur
    cfv
    c.1
    @11
    cR
    cur
    fveq2
    minmar1fval.o
    syl6eqr
    @22
    @15
    cR
    c0g
    cfv
    c.0
    @11
    cR
    c0g
    fveq2
    minmar1fval.z
    syl6eqr
    ifeq12d
    ifeq1d
    adantl
    mpt2eq123dv
    mpt2eq123dv
    mpteq12dv
    vi
    vj
    vk
    vm
    vn
    vr
    vl
    df-minmar1
    #
    vm
    cB
    @7
    cB
    @24
    cvv
    minmar1fval.b
    cA
    cbs
    fvex
    eqeltri
    mptex
    ovmpt2a
    @9
    wn
    #
    @0
    vm
    c0
    @7
    cmpt
    #
    @8
    @28
    @0
    c0
    @29
    vn
    vr
    @20
    cminmar1
    cN
    cR
    cvv
    cvv
    @27
    mpt2ndm0
    vm
    @7
    mpt0
    syl6eqr
    @28
    vm
    cB
    c0
    @7
    @28
    cB
    @25
    cbs
    cfv
    #
    c0
    cB
    @24
    @30
    minmar1fval.b
    cA
    @25
    cbs
    minmar1fval.a
    fveq2i
    eqtri
    cR
    cN
    matbas0pc
    syl5eq
    mpteq1d
    eqtr4d
    pm2.61i
    eqtri
end
