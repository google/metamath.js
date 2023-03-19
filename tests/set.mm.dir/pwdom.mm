include "cdom.mm"
include "wbr.mm"
include "cpw.mm"
include "c0.mm"
include "wceq.mm"
include "pweq.mm"
include "breq1d.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "csdm.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "reldom.mm"
include "brrelexi.mm"
include "0sdomg.mm"
include "syl.mm"
include "biimpar.mm"
include "simpl.mm"
include "fodomr.mm"
include "syl2anc.mm"
include "vex.mm"
include "fopwdom.mm"
include "mpan.mm"
include "exlimiv.mm"
include "wss.mm"
include "brrelex2i.mm"
include "pwexg.mm"
include "0ss.mm"
include "sspwb.mm"
include "mpbi.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "pm2.61ne.mm"

theorem pwdom
  let cA: class A
  let cB: class B
  let vf: setvar f


  assert |- ( A ~<_ B -> ~P A ~<_ ~P B )

  proof
    cA
    cB
    cdom
    wbr
    #
    cA
    cpw
    #
    cB
    cpw
    #
    cdom
    wbr
    #
    c0
    cpw
    #
    @2
    cdom
    wbr
    #
    cA
    c0
    cA
    c0
    wceq
    @1
    @4
    @2
    cdom
    cA
    c0
    pweq
    breq1d
    @0
    cA
    c0
    wne
    #
    wa
    #
    cB
    cA
    vf
    cv
    #
    wfo
    #
    vf
    wex
    #
    @3
    @7
    c0
    cA
    csdm
    wbr
    #
    @0
    @10
    @0
    @11
    @6
    @0
    cA
    cvv
    wcel
    @11
    @6
    wb
    cA
    cB
    cdom
    reldom
    brrelexi
    cA
    cvv
    0sdomg
    syl
    biimpar
    @0
    @6
    simpl
    cB
    cA
    vf
    fodomr
    syl2anc
    @9
    @3
    vf
    @8
    cvv
    wcel
    @9
    @3
    vf
    vex
    cB
    cA
    @8
    cvv
    fopwdom
    mpan
    exlimiv
    syl
    @0
    @2
    cvv
    wcel
    #
    @4
    @2
    wss
    #
    @5
    @0
    cB
    cvv
    wcel
    @12
    cA
    cB
    cdom
    reldom
    brrelex2i
    cB
    cvv
    pwexg
    syl
    c0
    cB
    wss
    @13
    cB
    0ss
    c0
    cB
    sspwb
    mpbi
    @4
    @2
    cvv
    ssdomg
    mpisyl
    pm2.61ne
end
