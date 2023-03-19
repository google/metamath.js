include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "ccpmat2mat.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "cco1.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cvv.mm"
include "ccpmat.mm"
include "wceq.mm"
include "df-cpmat2mat.mm"
include "a1i.mm"
include "oveq12.mm"
include "syl6eqr.mm"
include "simpl.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "elex.mm"
include "ovex.mm"
include "eqeltri.mm"
include "mptexg.mm"
include "mp1i.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem cpm2mfval
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let vm: setvar m
  let cI: class I
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vr: setvar r
  assume cpm2mfval.i: |- I = ( N cPolyMatToMat R )
  assume cpm2mfval.s: |- S = ( N ConstPolyMat R )

  disjoint N m
  disjoint N x
  disjoint N y
  disjoint m x
  disjoint m y
  disjoint x y
  disjoint R m
  disjoint R x
  disjoint R y
  disjoint S m
  disjoint N n
  disjoint N r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint r x
  disjoint r y
  disjoint R n
  disjoint R r
  disjoint S n
  disjoint S r
  disjoint V n
  disjoint V r
  assert |- ( ( N e. Fin /\ R e. V ) -> I = ( m e. S |-> ( x e. N , y e. N |-> ( ( coe1 ` ( x m y ) ) ` 0 ) ) ) )

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
    cI
    cN
    cR
    ccpmat2mat
    co
    vm
    cS
    vx
    vy
    cN
    cN
    cc0
    vx
    cv
    vy
    cv
    vm
    cv
    co
    cco1
    cfv
    cfv
    #
    cmpt2
    #
    cmpt
    #
    cpm2mfval.i
    @2
    vn
    vr
    cN
    cR
    cfn
    cvv
    vm
    vn
    cv
    #
    vr
    cv
    #
    ccpmat
    co
    #
    vx
    vy
    @6
    @6
    @3
    cmpt2
    #
    cmpt
    #
    @5
    ccpmat2mat
    cvv
    ccpmat2mat
    vn
    vr
    cfn
    cvv
    @10
    cmpt2
    wceq
    @2
    vx
    vy
    vm
    vn
    vr
    df-cpmat2mat
    a1i
    @6
    cN
    wceq
    #
    @7
    cR
    wceq
    #
    wa
    #
    @10
    @5
    wceq
    @2
    @13
    vm
    @8
    @9
    cS
    @4
    @13
    @8
    cN
    cR
    ccpmat
    co
    #
    cS
    @6
    cN
    @7
    cR
    ccpmat
    oveq12
    cpm2mfval.s
    syl6eqr
    @13
    vx
    vy
    @6
    @6
    @3
    cN
    cN
    @3
    @11
    @12
    simpl
    #
    @15
    @13
    @3
    eqidd
    mpt2eq123dv
    mpteq12dv
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
    cS
    cvv
    wcel
    @5
    cvv
    wcel
    @2
    cS
    @14
    cvv
    cpm2mfval.s
    cN
    cR
    ccpmat
    ovex
    eqeltri
    vm
    cS
    @4
    cvv
    mptexg
    mp1i
    ovmpt2d
    syl5eq
end
