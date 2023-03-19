include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "simpr.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "ssrexv.mm"
include "ad2antlr.mm"
include "cvv.mm"
include "wb.mm"
include "c0.mm"
include "n0i.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "restfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "nsyl2.mm"
include "adantl.mm"
include "elrest.mm"
include "syl.mm"
include "simpll.mm"
include "simprd.mm"
include "syl2anc.mm"
include "3imtr4d.mm"
include "mpd.mm"
include "ex.mm"
include "ssrdv.mm"

theorem ssrest
  let cA: class A
  let cJ: class J
  let cK: class K
  let cV: class V
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C


  assert |- ( ( K e. V /\ J C_ K ) -> ( J |`t A ) C_ ( K |`t A ) )

  proof
    cK
    cV
    wcel
    #
    cJ
    cK
    wss
    #
    wa
    #
    vx
    cJ
    cA
    crest
    co
    #
    cK
    cA
    crest
    co
    #
    @2
    vx
    cv
    #
    @3
    wcel
    #
    @5
    @4
    wcel
    #
    @2
    @6
    wa
    #
    @6
    @7
    @2
    @6
    simpr
    @8
    @5
    vy
    cv
    cA
    cin
    wceq
    #
    vy
    cJ
    wrex
    #
    @9
    vy
    cK
    wrex
    #
    @6
    @7
    @1
    @10
    @11
    wi
    @0
    @6
    @9
    vy
    cJ
    cK
    ssrexv
    ad2antlr
    @8
    cJ
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    wa
    #
    @6
    @10
    wb
    @6
    @14
    @2
    @6
    @3
    c0
    wceq
    @14
    @3
    @5
    n0i
    cJ
    cA
    cvv
    crest
    crest
    cvv
    cvv
    cxp
    #
    wfn
    crest
    cdm
    @15
    wceq
    restfn
    @15
    crest
    fndm
    ax-mp
    ndmov
    nsyl2
    adantl
    #
    vy
    @5
    cA
    cJ
    cvv
    cvv
    elrest
    syl
    @8
    @0
    @13
    @7
    @11
    wb
    @0
    @1
    @6
    simpll
    @8
    @12
    @13
    @16
    simprd
    vy
    @5
    cA
    cK
    cV
    cvv
    elrest
    syl2anc
    3imtr4d
    mpd
    ex
    ssrdv
end
