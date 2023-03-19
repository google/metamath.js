include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cdmat.mm"
include "co.mm"
include "cv.mm"
include "wne.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "cvv.mm"
include "c0g.mm"
include "cfv.mm"
include "cmat.mm"
include "cbs.mm"
include "cmpt2.mm"
include "df-dmat.mm"
include "a1i.mm"
include "oveq12.mm"
include "fveq2d.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "simpl.mm"
include "fveq2.mm"
include "adantl.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "elex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabexg.mm"
include "mp1i.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem dmatval
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let cN: class N
  let cV: class V
  let c.0: class .0.
  let vn: setvar n
  let vr: setvar r
  assume dmatval.a: |- A = ( N Mat R )
  assume dmatval.b: |- B = ( Base ` A )
  assume dmatval.0: |- .0. = ( 0g ` R )
  assume dmatval.d: |- D = ( N DMat R )

  disjoint B m
  disjoint N i
  disjoint N j
  disjoint N m
  disjoint i j
  disjoint i m
  disjoint j m
  disjoint R i
  disjoint R j
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
  disjoint R n
  disjoint R r
  disjoint V n
  disjoint V r
  disjoint .0. n
  disjoint .0. r
  assert |- ( ( N e. Fin /\ R e. V ) -> D = { m e. B | A. i e. N A. j e. N ( i =/= j -> ( i m j ) = .0. ) } )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    #
    cD
    cN
    cR
    cdmat
    co
    vi
    cv
    #
    vj
    cv
    #
    wne
    #
    @3
    @4
    vm
    cv
    co
    #
    c.0
    wceq
    #
    wi
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    vm
    cB
    crab
    #
    dmatval.d
    @2
    vn
    vr
    cN
    cR
    cfn
    cvv
    @5
    @6
    vr
    cv
    #
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vj
    vn
    cv
    #
    wral
    #
    vi
    @16
    wral
    #
    vm
    @16
    @12
    cmat
    co
    #
    cbs
    cfv
    #
    crab
    #
    @11
    cdmat
    cvv
    cdmat
    vn
    vr
    cfn
    cvv
    @21
    cmpt2
    wceq
    @2
    vi
    vj
    vm
    vn
    vr
    df-dmat
    a1i
    @16
    cN
    wceq
    #
    @12
    cR
    wceq
    #
    wa
    #
    @21
    @11
    wceq
    @2
    @24
    @18
    @10
    vm
    @20
    cB
    @24
    @20
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    cB
    @24
    @19
    @25
    cbs
    @16
    cN
    @12
    cR
    cmat
    oveq12
    fveq2d
    cB
    cA
    cbs
    cfv
    #
    @26
    dmatval.b
    cA
    @25
    cbs
    dmatval.a
    fveq2i
    eqtri
    syl6eqr
    @24
    @17
    @9
    vi
    @16
    cN
    @22
    @23
    simpl
    #
    @24
    @15
    @8
    vj
    @16
    cN
    @28
    @24
    @14
    @7
    @5
    @24
    @13
    c.0
    @6
    @23
    @13
    c.0
    wceq
    @22
    @23
    @13
    cR
    c0g
    cfv
    c.0
    @12
    cR
    c0g
    fveq2
    dmatval.0
    syl6eqr
    adantl
    eqeq2d
    imbi2d
    raleqbidv
    raleqbidv
    rabeqbidv
    adantl
    @0
    @1
    simpl
    @1
    cR
    cvv
    wcel
    @0
    cR
    cV
    elex
    adantl
    cB
    cvv
    wcel
    @11
    cvv
    wcel
    @2
    cB
    @27
    cvv
    dmatval.b
    cA
    cbs
    fvex
    eqeltri
    @10
    vm
    cB
    cvv
    rabexg
    mp1i
    ovmpt2d
    syl5eq
end
