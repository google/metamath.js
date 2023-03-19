include "wcel.mm"
include "cvv.mm"
include "clcd.mm"
include "cfv.mm"
include "cv.mm"
include "cdvh.mm"
include "cld.mm"
include "clk.mm"
include "coch.mm"
include "wceq.mm"
include "clfn.mm"
include "crab.mm"
include "cress.mm"
include "co.mm"
include "cmpt.mm"
include "elex.mm"
include "clh.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "fveq12d.mm"
include "eqeq12d.mm"
include "rabeqbidv.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "df-lcdual.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem lcdfval
  let vw: setvar w
  let vf: setvar f
  let cH: class H
  let cK: class K
  let cX: class X
  let vk: setvar k
  assume lcdval.h: |- H = ( LHyp ` K )

  disjoint H w
  disjoint f w
  disjoint K f
  disjoint K w
  disjoint k w
  disjoint H k
  disjoint f k
  disjoint K k
  assert |- ( K e. X -> ( LCDual ` K ) = ( w e. H |-> ( ( LDual ` ( ( DVecH ` K ) ` w ) ) |`s { f e. ( LFnl ` ( ( DVecH ` K ) ` w ) ) | ( ( ( ocH ` K ) ` w ) ` ( ( ( ocH ` K ) ` w ) ` ( ( LKer ` ( ( DVecH ` K ) ` w ) ) ` f ) ) ) = ( ( LKer ` ( ( DVecH ` K ) ` w ) ) ` f ) } ) ) )

  proof
    cK
    cX
    wcel
    cK
    cvv
    wcel
    cK
    clcd
    cfv
    vw
    cH
    vw
    cv
    #
    cK
    cdvh
    cfv
    #
    cfv
    #
    cld
    cfv
    #
    vf
    cv
    #
    @2
    clk
    cfv
    #
    cfv
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
    @8
    cfv
    #
    @6
    wceq
    #
    vf
    @2
    clfn
    cfv
    #
    crab
    #
    cress
    co
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
    @0
    @16
    cdvh
    cfv
    #
    cfv
    #
    cld
    cfv
    #
    @4
    @19
    clk
    cfv
    #
    cfv
    #
    @0
    @16
    coch
    cfv
    #
    cfv
    #
    cfv
    #
    @24
    cfv
    #
    @22
    wceq
    #
    vf
    @19
    clfn
    cfv
    #
    crab
    #
    cress
    co
    #
    cmpt
    @15
    cvv
    clcd
    @16
    cK
    wceq
    #
    vw
    @17
    @30
    cH
    @14
    @31
    @17
    cK
    clh
    cfv
    #
    cH
    @16
    cK
    clh
    fveq2
    lcdval.h
    syl6eqr
    @31
    @20
    @3
    @29
    @13
    cress
    @31
    @19
    @2
    cld
    @31
    @0
    @18
    @1
    @16
    cK
    cdvh
    fveq2
    fveq1d
    #
    fveq2d
    @31
    @27
    @11
    vf
    @28
    @12
    @31
    @19
    @2
    clfn
    @33
    fveq2d
    @31
    @26
    @10
    @22
    @6
    @31
    @25
    @9
    @24
    @8
    @31
    @0
    @23
    @7
    @16
    cK
    coch
    fveq2
    fveq1d
    #
    @31
    @22
    @6
    @24
    @8
    @34
    @31
    @4
    @21
    @5
    @31
    @19
    @2
    clk
    @33
    fveq2d
    fveq1d
    #
    fveq12d
    fveq12d
    @35
    eqeq12d
    rabeqbidv
    oveq12d
    mpteq12dv
    vw
    vf
    vk
    df-lcdual
    vw
    cH
    @14
    cH
    @32
    cvv
    lcdval.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
