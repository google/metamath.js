include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "c0.mm"
include "wceq.mm"
include "simpr.mm"
include "0ex.mm"
include "syl6eqel.mm"
include "wne.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "csn.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "snex.mm"
include "dmexg.mm"
include "rnexg.mm"
include "unexg.mm"
include "syl2anc.mm"
include "sylancr.mm"
include "ad2antlr.mm"
include "cdif.mm"
include "wss.mm"
include "sossfld.mm"
include "adantlr.mm"
include "ssundif.mm"
include "sylibr.mm"
include "ssexd.mm"
include "ex.mm"
include "exlimdv.mm"
include "imp.mm"
include "sylan2b.mm"
include "pm2.61dane.mm"

theorem soex
  let cA: class A
  let cR: class R
  let cV: class V
  let vx: setvar x


  assert |- ( ( R Or A /\ R e. V ) -> A e. _V )

  proof
    cA
    cR
    wor
    #
    cR
    cV
    wcel
    #
    wa
    #
    cA
    cvv
    wcel
    #
    cA
    c0
    @2
    cA
    c0
    wceq
    #
    wa
    cA
    c0
    cvv
    @2
    @4
    simpr
    0ex
    syl6eqel
    cA
    c0
    wne
    @2
    vx
    cv
    #
    cA
    wcel
    #
    vx
    wex
    #
    @3
    vx
    cA
    n0
    @2
    @7
    @3
    @2
    @6
    @3
    vx
    @2
    @6
    @3
    @2
    @6
    wa
    #
    cA
    @5
    csn
    #
    cR
    cdm
    #
    cR
    crn
    #
    cun
    #
    cun
    #
    cvv
    @1
    @13
    cvv
    wcel
    #
    @0
    @6
    @1
    @9
    cvv
    wcel
    @12
    cvv
    wcel
    #
    @14
    @5
    snex
    @1
    @10
    cvv
    wcel
    @11
    cvv
    wcel
    @15
    cR
    cV
    dmexg
    cR
    cV
    rnexg
    @10
    @11
    cvv
    cvv
    unexg
    syl2anc
    @9
    @12
    cvv
    cvv
    unexg
    sylancr
    ad2antlr
    @8
    cA
    @9
    cdif
    @12
    wss
    #
    cA
    @13
    wss
    @0
    @6
    @16
    @1
    cA
    @5
    cR
    sossfld
    adantlr
    cA
    @9
    @12
    ssundif
    sylibr
    ssexd
    ex
    exlimdv
    imp
    sylan2b
    pm2.61dane
end
