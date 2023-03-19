include "cmgm.mm"
include "wcel.mm"
include "csubmgm.mm"
include "cfv.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cpw.mm"
include "crab.mm"
include "cacs.mm"
include "wa.mm"
include "cab.mm"
include "wss.mm"
include "eqid.mm"
include "issubmgm.mm"
include "selpw.mm"
include "anbi1i.mm"
include "syl6bbr.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6eqr.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mgmcl.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "acsfn2.mm"
include "sylancr.mm"
include "eqeltrd.mm"

theorem submgmacs
  let cB: class B
  let cG: class G
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume submgmacs.b: |- B = ( Base ` G )


  assert |- ( G e. Mgm -> ( SubMgm ` G ) e. ( ACS ` B ) )

  proof
    cG
    cmgm
    wcel
    #
    cG
    csubmgm
    cfv
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
    vs
    cv
    #
    wcel
    vy
    @6
    wral
    vx
    @6
    wral
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
    @6
    @8
    wcel
    #
    @7
    wa
    #
    vs
    cab
    @9
    @0
    @12
    vs
    @1
    @0
    @6
    @1
    wcel
    @6
    cB
    wss
    #
    @7
    wa
    @12
    vx
    vy
    cB
    @4
    @6
    cG
    submgmacs.b
    @4
    eqid
    #
    issubmgm
    @11
    @13
    @7
    vs
    cB
    selpw
    anbi1i
    syl6bbr
    abbi2dv
    @7
    vs
    @8
    df-rab
    syl6eqr
    @0
    cB
    cvv
    wcel
    @5
    cB
    wcel
    #
    vy
    cB
    wral
    vx
    cB
    wral
    @9
    @10
    wcel
    cB
    cG
    cbs
    cfv
    cvv
    submgmacs.b
    cG
    cbs
    fvex
    eqeltri
    @0
    @15
    vx
    vy
    cB
    cB
    @0
    @2
    cB
    wcel
    @3
    cB
    wcel
    @15
    cB
    cG
    @2
    @3
    @4
    submgmacs.b
    @14
    mgmcl
    3expb
    ralrimivva
    @5
    cvv
    cB
    vs
    vx
    vy
    acsfn2
    sylancr
    eqeltrd
end
