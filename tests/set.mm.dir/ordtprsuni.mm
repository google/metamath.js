include "cpreset.mm"
include "wcel.mm"
include "cdm.mm"
include "csn.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "cuni.mm"
include "prsdm.mm"
include "sneqd.mm"
include "biidd.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "uneq12d.mm"
include "unieqd.mm"
include "cvv.mm"
include "wceq.mm"
include "cple.mm"
include "cfv.mm"
include "cxp.mm"
include "cin.mm"
include "fvex.mm"
include "inex1.mm"
include "eqeltri.mm"
include "eqid.mm"
include "ordtuni.mm"
include "ax-mp.mm"
include "syl5reqr.mm"
include "uneq12i.mm"
include "a1i.mm"
include "uneq2d.mm"
include "3eqtr4d.mm"

theorem ordtprsuni
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
  assert |- ( K e. Preset -> B = U. ( { B } u. ( E u. F ) ) )

  proof
    cK
    cpreset
    wcel
    #
    c.le
    cdm
    #
    csn
    #
    vx
    @1
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
    @1
    crab
    #
    cmpt
    #
    crn
    #
    vx
    @1
    @4
    @3
    c.le
    wbr
    wn
    #
    vy
    @1
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
    cuni
    #
    cB
    csn
    #
    vx
    cB
    @5
    vy
    cB
    crab
    #
    cmpt
    #
    crn
    #
    vx
    cB
    @9
    vy
    cB
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
    cuni
    cB
    @16
    cE
    cF
    cun
    #
    cun
    #
    cuni
    @0
    @14
    @24
    @0
    @2
    @16
    @13
    @23
    @0
    @1
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
    @8
    @19
    @12
    @22
    @0
    @7
    @18
    @0
    vx
    @1
    @6
    cB
    @17
    @27
    @0
    @5
    @5
    vy
    @1
    cB
    @27
    @0
    @5
    biidd
    rabeqbidv
    mpteq12dv
    rneqd
    @0
    @11
    @21
    @0
    vx
    @1
    @10
    cB
    @20
    @27
    @0
    @9
    @9
    vy
    @1
    cB
    @27
    @0
    @9
    biidd
    rabeqbidv
    mpteq12dv
    rneqd
    uneq12d
    uneq12d
    unieqd
    @0
    @15
    @1
    cB
    c.le
    cvv
    wcel
    @1
    @15
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
    @28
    @29
    cK
    cple
    fvex
    inex1
    eqeltri
    vx
    vy
    @8
    @12
    c.le
    cvv
    @1
    @1
    eqid
    @8
    eqid
    @12
    eqid
    ordtuni
    ax-mp
    @27
    syl5reqr
    @0
    @26
    @24
    @0
    @25
    @23
    @16
    @25
    @23
    wceq
    @0
    cE
    @19
    cF
    @22
    ordtposval.e
    ordtposval.f
    uneq12i
    a1i
    uneq2d
    unieqd
    3eqtr4d
end
