include "cvv.mm"
include "wcel.mm"
include "cid.mm"
include "cfv.mm"
include "cxp.mm"
include "wceq.mm"
include "wn.mm"
include "c0.mm"
include "0xp.mm"
include "fvprc.mm"
include "xpeq1d.mm"
include "wa.mm"
include "simpr.mm"
include "xpeq2d.mm"
include "xp0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "0ex.mm"
include "fvi.mm"
include "ax-mp.mm"
include "wne.mm"
include "cdm.mm"
include "dmexg.mm"
include "dmxp.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "con3d.mm"
include "impcom.mm"
include "syl.mm"
include "pm2.61dane.mm"
include "3eqtr4a.mm"
include "crn.mm"
include "rnexg.mm"
include "rnxp.mm"
include "xpeq12.mm"
include "syl2an.mm"
include "xpexg.mm"
include "eqtr4d.mm"
include "ecase.mm"

theorem txindislem
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  let cW: class W


  assert |- ( ( _I ` A ) X. ( _I ` B ) ) = ( _I ` ( A X. B ) )

  proof
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    cA
    cid
    cfv
    #
    cB
    cid
    cfv
    #
    cxp
    #
    cA
    cB
    cxp
    #
    cid
    cfv
    #
    wceq
    @0
    wn
    #
    c0
    @3
    cxp
    c0
    @4
    @6
    @3
    0xp
    @7
    @2
    c0
    @3
    cA
    cid
    fvprc
    xpeq1d
    @7
    @6
    c0
    wceq
    #
    cB
    c0
    @7
    cB
    c0
    wceq
    #
    wa
    #
    @6
    c0
    cid
    cfv
    #
    c0
    @10
    @5
    c0
    cid
    @10
    @5
    cA
    c0
    cxp
    c0
    @10
    cB
    c0
    cA
    @7
    @9
    simpr
    xpeq2d
    cA
    xp0
    syl6eq
    fveq2d
    c0
    cvv
    wcel
    @11
    c0
    wceq
    0ex
    c0
    cvv
    fvi
    ax-mp
    #
    syl6eq
    @7
    cB
    c0
    wne
    #
    wa
    @5
    cvv
    wcel
    #
    wn
    #
    @8
    @13
    @7
    @15
    @13
    @14
    @0
    @14
    @5
    cdm
    #
    cvv
    wcel
    @13
    @0
    @5
    cvv
    dmexg
    @13
    @16
    cA
    cvv
    cA
    cB
    dmxp
    eleq1d
    syl5ib
    con3d
    impcom
    @5
    cid
    fvprc
    #
    syl
    pm2.61dane
    3eqtr4a
    @1
    wn
    #
    @2
    c0
    cxp
    c0
    @4
    @6
    @2
    xp0
    @18
    @3
    c0
    @2
    cB
    cid
    fvprc
    xpeq2d
    @18
    @8
    cA
    c0
    @18
    cA
    c0
    wceq
    #
    wa
    #
    @6
    @11
    c0
    @20
    @5
    c0
    cid
    @20
    @5
    c0
    cB
    cxp
    c0
    @20
    cA
    c0
    cB
    @18
    @19
    simpr
    xpeq1d
    cB
    0xp
    syl6eq
    fveq2d
    @12
    syl6eq
    @18
    cA
    c0
    wne
    #
    wa
    @15
    @8
    @21
    @18
    @15
    @21
    @14
    @1
    @14
    @5
    crn
    #
    cvv
    wcel
    @21
    @1
    @5
    cvv
    rnexg
    @21
    @22
    cB
    cvv
    cA
    cB
    rnxp
    eleq1d
    syl5ib
    con3d
    impcom
    @17
    syl
    pm2.61dane
    3eqtr4a
    @0
    @1
    wa
    #
    @4
    @5
    @6
    @0
    @2
    cA
    wceq
    @3
    cB
    wceq
    @4
    @5
    wceq
    @1
    cA
    cvv
    fvi
    cB
    cvv
    fvi
    @2
    cA
    @3
    cB
    xpeq12
    syl2an
    @23
    @14
    @6
    @5
    wceq
    cA
    cB
    cvv
    cvv
    xpexg
    @5
    cvv
    fvi
    syl
    eqtr4d
    ecase
end
