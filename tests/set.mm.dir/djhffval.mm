include "wcel.mm"
include "cvv.mm"
include "cdjh.mm"
include "cfv.mm"
include "cv.mm"
include "cdvh.mm"
include "cbs.mm"
include "cpw.mm"
include "coch.mm"
include "cin.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "clh.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "pweqd.mm"
include "ineq12d.mm"
include "fveq12d.mm"
include "mpt2eq123dv.mm"
include "mpteq12dv.mm"
include "df-djh.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem djhffval
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cH: class H
  let cK: class K
  let cX: class X
  let vk: setvar k
  assume djhval.h: |- H = ( LHyp ` K )

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
  assert |- ( K e. X -> ( joinH ` K ) = ( w e. H |-> ( x e. ~P ( Base ` ( ( DVecH ` K ) ` w ) ) , y e. ~P ( Base ` ( ( DVecH ` K ) ` w ) ) |-> ( ( ( ocH ` K ) ` w ) ` ( ( ( ( ocH ` K ) ` w ) ` x ) i^i ( ( ( ocH ` K ) ` w ) ` y ) ) ) ) ) )

  proof
    cK
    cX
    wcel
    cK
    cvv
    wcel
    cK
    cdjh
    cfv
    vw
    cH
    vx
    vy
    vw
    cv
    #
    cK
    cdvh
    cfv
    #
    cfv
    #
    cbs
    cfv
    #
    cpw
    #
    @4
    vx
    cv
    #
    @0
    cK
    coch
    cfv
    #
    cfv
    #
    cfv
    #
    vy
    cv
    #
    @7
    cfv
    #
    cin
    #
    @7
    cfv
    #
    cmpt2
    #
    cmpt
    #
    wceq
    cK
    cX
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
    @15
    cdvh
    cfv
    #
    cfv
    #
    cbs
    cfv
    #
    cpw
    #
    @20
    @5
    @0
    @15
    coch
    cfv
    #
    cfv
    #
    cfv
    #
    @9
    @22
    cfv
    #
    cin
    #
    @22
    cfv
    #
    cmpt2
    #
    cmpt
    @14
    cvv
    cdjh
    @15
    cK
    wceq
    #
    vw
    @16
    @27
    cH
    @13
    @28
    @16
    cK
    clh
    cfv
    #
    cH
    @15
    cK
    clh
    fveq2
    djhval.h
    syl6eqr
    @28
    vx
    vy
    @20
    @20
    @26
    @4
    @4
    @12
    @28
    @19
    @3
    @28
    @18
    @2
    cbs
    @28
    @0
    @17
    @1
    @15
    cK
    cdvh
    fveq2
    fveq1d
    fveq2d
    pweqd
    #
    @30
    @28
    @25
    @11
    @22
    @7
    @28
    @0
    @21
    @6
    @15
    cK
    coch
    fveq2
    fveq1d
    #
    @28
    @23
    @8
    @24
    @10
    @28
    @5
    @22
    @7
    @31
    fveq1d
    @28
    @9
    @22
    @7
    @31
    fveq1d
    ineq12d
    fveq12d
    mpt2eq123dv
    mpteq12dv
    vx
    vy
    vw
    vk
    df-djh
    vw
    cH
    @13
    cH
    @29
    cvv
    djhval.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
