include "cpreset.mm"
include "wcel.mm"
include "cordt.mm"
include "cfv.mm"
include "cdm.mm"
include "csn.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "cfi.mm"
include "ctg.mm"
include "cvv.mm"
include "wceq.mm"
include "cple.mm"
include "cxp.mm"
include "cin.mm"
include "fvex.mm"
include "inex1.mm"
include "eqeltri.mm"
include "eqid.mm"
include "ordtval.mm"
include "ax-mp.mm"
include "prsdm.mm"
include "sneqd.mm"
include "rabeq.mm"
include "syl.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "syl6eqr.mm"
include "uneq12d.mm"
include "fveq2d.mm"
include "syl5eq.mm"

theorem ordtprsval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cE: class E
  let cF: class F
  let cK: class K
  let c.le: class .<_
  assume ordtNEW.b: |- B = ( Base ` K )
  assume ordtNEW.l: |- .<_ = ( ( le ` K ) i^i ( B X. B ) )
  assume ordtposval.e: |- E = ran ( x e. B |-> { y e. B | -. y .<_ x } )
  assume ordtposval.f: |- F = ran ( x e. B |-> { y e. B | -. x .<_ y } )

  disjoint x y
  disjoint .<_ x
  disjoint .<_ y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  assert |- ( K e. Preset -> ( ordTop ` .<_ ) = ( topGen ` ( fi ` ( { B } u. ( E u. F ) ) ) ) )

  proof
    cK
    cpreset
    wcel
    #
    c.le
    cordt
    cfv
    #
    c.le
    cdm
    #
    csn
    #
    vx
    @2
    vy
    cv
    #
    vx
    cv
    #
    c.le
    wbr
    wn
    #
    vy
    @2
    crab
    #
    cmpt
    #
    crn
    #
    vx
    @2
    @5
    @4
    c.le
    wbr
    wn
    #
    vy
    @2
    crab
    #
    cmpt
    #
    crn
    #
    cun
    #
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    cB
    csn
    #
    cE
    cF
    cun
    #
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    c.le
    cvv
    wcel
    @1
    @17
    wceq
    c.le
    cK
    cple
    cfv
    #
    cB
    cB
    cxp
    #
    cin
    cvv
    ordtNEW.l
    @22
    @23
    cK
    cple
    fvex
    inex1
    eqeltri
    vx
    vy
    @9
    @13
    c.le
    cvv
    @2
    @2
    eqid
    @9
    eqid
    @13
    eqid
    ordtval
    ax-mp
    @0
    @16
    @21
    ctg
    @0
    @15
    @20
    cfi
    @0
    @3
    @18
    @14
    @19
    @0
    @2
    cB
    cB
    cK
    c.le
    ordtNEW.b
    ordtNEW.l
    prsdm
    #
    sneqd
    @0
    @9
    cE
    @13
    cF
    @0
    @9
    vx
    cB
    @6
    vy
    cB
    crab
    #
    cmpt
    #
    crn
    cE
    @0
    @8
    @26
    @0
    vx
    @2
    @7
    cB
    @25
    @24
    @0
    @2
    cB
    wceq
    #
    @7
    @25
    wceq
    @24
    @6
    vy
    @2
    cB
    rabeq
    syl
    mpteq12dv
    rneqd
    ordtposval.e
    syl6eqr
    @0
    @13
    vx
    cB
    @10
    vy
    cB
    crab
    #
    cmpt
    #
    crn
    cF
    @0
    @12
    @29
    @0
    vx
    @2
    @11
    cB
    @28
    @24
    @0
    @27
    @11
    @28
    wceq
    @24
    @10
    vy
    @2
    cB
    rabeq
    syl
    mpteq12dv
    rneqd
    ordtposval.f
    syl6eqr
    uneq12d
    uneq12d
    fveq2d
    fveq2d
    syl5eq
end
