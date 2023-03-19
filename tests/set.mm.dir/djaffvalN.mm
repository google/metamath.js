include "wcel.mm"
include "cvv.mm"
include "cdjaN.mm"
include "cfv.mm"
include "cv.mm"
include "cltrn.mm"
include "cpw.mm"
include "cocaN.mm"
include "cin.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "clh.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "pweqd.mm"
include "ineq12d.mm"
include "fveq12d.mm"
include "mpt2eq123dv.mm"
include "mpteq12dv.mm"
include "df-djaN.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem djaffvalN
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cH: class H
  let cK: class K
  let cV: class V
  let vk: setvar k
  assume djaval.h: |- H = ( LHyp ` K )

  disjoint H w
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint x y
  disjoint K x
  disjoint K y
  disjoint k w
  disjoint H k
  disjoint k x
  disjoint k y
  disjoint K k
  assert |- ( K e. V -> ( vA ` K ) = ( w e. H |-> ( x e. ~P ( ( LTrn ` K ) ` w ) , y e. ~P ( ( LTrn ` K ) ` w ) |-> ( ( ( ocA ` K ) ` w ) ` ( ( ( ( ocA ` K ) ` w ) ` x ) i^i ( ( ( ocA ` K ) ` w ) ` y ) ) ) ) ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    cK
    cdjaN
    cfv
    vw
    cH
    vx
    vy
    vw
    cv
    #
    cK
    cltrn
    cfv
    #
    cfv
    #
    cpw
    #
    @3
    vx
    cv
    #
    @0
    cK
    cocaN
    cfv
    #
    cfv
    #
    cfv
    #
    vy
    cv
    #
    @6
    cfv
    #
    cin
    #
    @6
    cfv
    #
    cmpt2
    #
    cmpt
    #
    wceq
    cK
    cV
    elex
    vk
    cK
    vw
    vk
    cv
    #
    clh
    cfv
    #
    vx
    vy
    @0
    @14
    cltrn
    cfv
    #
    cfv
    #
    cpw
    #
    @18
    @4
    @0
    @14
    cocaN
    cfv
    #
    cfv
    #
    cfv
    #
    @8
    @20
    cfv
    #
    cin
    #
    @20
    cfv
    #
    cmpt2
    #
    cmpt
    @13
    cvv
    cdjaN
    @14
    cK
    wceq
    #
    vw
    @15
    @25
    cH
    @12
    @26
    @15
    cK
    clh
    cfv
    #
    cH
    @14
    cK
    clh
    fveq2
    djaval.h
    syl6eqr
    @26
    vx
    vy
    @18
    @18
    @24
    @3
    @3
    @11
    @26
    @17
    @2
    @26
    @0
    @16
    @1
    @14
    cK
    cltrn
    fveq2
    fveq1d
    pweqd
    #
    @28
    @26
    @23
    @10
    @20
    @6
    @26
    @0
    @19
    @5
    @14
    cK
    cocaN
    fveq2
    fveq1d
    #
    @26
    @21
    @7
    @22
    @9
    @26
    @4
    @20
    @6
    @29
    fveq1d
    @26
    @8
    @20
    @6
    @29
    fveq1d
    ineq12d
    fveq12d
    mpt2eq123dv
    mpteq12dv
    vx
    vy
    vw
    vk
    df-djaN
    vw
    cH
    @12
    cH
    @27
    cvv
    djaval.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
