include "cmnd.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cfv.mm"
include "c0g.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cpw.mm"
include "crab.mm"
include "cacs.mm"
include "cab.mm"
include "wss.mm"
include "w3a.mm"
include "eqid.mm"
include "issubm.mm"
include "selpw.mm"
include "anbi1i.mm"
include "3anass.mm"
include "bitr4i.mm"
include "syl6bbr.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6eqr.mm"
include "cin.mm"
include "inrab.mm"
include "cmre.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mreacs.mm"
include "mp1i.mm"
include "mndidcl.mm"
include "acsfn0.mm"
include "sylancr.mm"
include "mndcl.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "acsfn2.mm"
include "mreincl.mm"
include "syl3anc.mm"
include "syl5eqelr.mm"
include "eqeltrd.mm"

theorem submacs
  let cB: class B
  let cG: class G
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume submacs.b: |- B = ( Base ` G )


  assert |- ( G e. Mnd -> ( SubMnd ` G ) e. ( ACS ` B ) )

  proof
    cG
    cmnd
    wcel
    #
    cG
    csubmnd
    cfv
    #
    cG
    c0g
    cfv
    #
    vs
    cv
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @3
    wcel
    vy
    @3
    wral
    vx
    @3
    wral
    #
    wa
    #
    vs
    cB
    cpw
    #
    crab
    #
    cB
    cacs
    cfv
    #
    @0
    @1
    @3
    @11
    wcel
    #
    @10
    wa
    #
    vs
    cab
    @12
    @0
    @15
    vs
    @1
    @0
    @3
    @1
    wcel
    @3
    cB
    wss
    #
    @4
    @9
    w3a
    #
    @15
    vx
    vy
    cB
    @7
    @3
    cG
    @2
    submacs.b
    @2
    eqid
    #
    @7
    eqid
    #
    issubm
    @15
    @16
    @10
    wa
    @17
    @14
    @16
    @10
    vs
    cB
    selpw
    anbi1i
    @16
    @4
    @9
    3anass
    bitr4i
    syl6bbr
    abbi2dv
    @10
    vs
    @11
    df-rab
    syl6eqr
    @0
    @12
    @4
    vs
    @11
    crab
    #
    @9
    vs
    @11
    crab
    #
    cin
    #
    @13
    @4
    @9
    vs
    @11
    inrab
    @0
    @13
    @11
    cmre
    cfv
    wcel
    #
    @20
    @13
    wcel
    #
    @21
    @13
    wcel
    #
    @22
    @13
    wcel
    cB
    cvv
    wcel
    #
    @23
    @0
    cB
    cG
    cbs
    cfv
    cvv
    submacs.b
    cG
    cbs
    fvex
    eqeltri
    #
    cvv
    cB
    mreacs
    mp1i
    @0
    @26
    @2
    cB
    wcel
    @24
    @27
    cB
    cG
    @2
    submacs.b
    @18
    mndidcl
    @2
    cvv
    cB
    vs
    acsfn0
    sylancr
    @0
    @26
    @8
    cB
    wcel
    #
    vy
    cB
    wral
    vx
    cB
    wral
    @25
    @27
    @0
    @28
    vx
    vy
    cB
    cB
    @0
    @5
    cB
    wcel
    @6
    cB
    wcel
    @28
    cB
    @7
    cG
    @5
    @6
    submacs.b
    @19
    mndcl
    3expb
    ralrimivva
    @8
    cvv
    cB
    vs
    vx
    vy
    acsfn2
    sylancr
    @20
    @21
    @13
    @11
    mreincl
    syl3anc
    syl5eqelr
    eqeltrd
end
