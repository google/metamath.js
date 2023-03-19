include "cch.mm"
include "wcel.mm"
include "cat.mm"
include "wa.mm"
include "ccv.mm"
include "wbr.mm"
include "c0h.mm"
include "wceq.mm"
include "wss.mm"
include "wpss.mm"
include "wi.mm"
include "atelch.mm"
include "cvpss.mm"
include "sylan2.mm"
include "ch0le.mm"
include "adantr.mm"
include "jctild.mm"
include "atcv0.mm"
include "h0elch.mm"
include "cvnbtwn3.mm"
include "mp3an1.mm"
include "sylan.mm"
include "mpd.mm"
include "ancoms.mm"
include "syld.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "adantl.mm"
include "impbid.mm"

theorem atcveq0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. HAtoms ) -> ( A <oH B <-> A = 0H ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cat
    wcel
    #
    wa
    #
    cA
    cB
    ccv
    wbr
    #
    cA
    c0h
    wceq
    #
    @2
    @3
    c0h
    cA
    wss
    #
    cA
    cB
    wpss
    #
    wa
    #
    @4
    @2
    @3
    @6
    @5
    @1
    @0
    cB
    cch
    wcel
    #
    @3
    @6
    wi
    cB
    atelch
    #
    cA
    cB
    cvpss
    sylan2
    @0
    @5
    @1
    cA
    ch0le
    adantr
    jctild
    @1
    @0
    @7
    @4
    wi
    #
    @1
    @0
    wa
    c0h
    cB
    ccv
    wbr
    #
    @10
    @1
    @11
    @0
    cB
    atcv0
    #
    adantr
    @1
    @8
    @0
    @11
    @10
    wi
    #
    @9
    c0h
    cch
    wcel
    @8
    @0
    @13
    h0elch
    c0h
    cB
    cA
    cvnbtwn3
    mp3an1
    sylan
    mpd
    ancoms
    syld
    @1
    @4
    @3
    wi
    @0
    @1
    @3
    @4
    @11
    @12
    cA
    c0h
    cB
    ccv
    breq1
    syl5ibrcom
    adantl
    impbid
end
