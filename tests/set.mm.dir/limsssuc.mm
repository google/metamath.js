include "wlim.mm"
include "wss.mm"
include "csuc.mm"
include "sssucid.mm"
include "sstr2.mm"
include "mpi.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "limsuc.mm"
include "biimpa.mm"
include "word.mm"
include "wb.mm"
include "limord.mm"
include "adantr.mm"
include "ordelord.mm"
include "sylan.mm"
include "ordsuc.mm"
include "sylib.mm"
include "ordtri1.mm"
include "syl2anc.mm"
include "con2bid.mm"
include "mpbid.mm"
include "ex.mm"
include "sylan9r.mm"
include "con2d.mm"
include "com23.mm"
include "imp31.mm"
include "wo.mm"
include "ssel2.mm"
include "vex.mm"
include "elsuc.mm"
include "ord.mm"
include "con1d.mm"
include "adantll.mm"
include "mpd.mm"
include "ssrdv.mm"
include "impbid2.mm"

theorem limsssuc
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( Lim A -> ( A C_ B <-> A C_ suc B ) )

  proof
    cA
    wlim
    #
    cA
    cB
    wss
    #
    cA
    cB
    csuc
    #
    wss
    #
    @1
    cB
    @2
    wss
    @3
    cB
    sssucid
    cA
    cB
    @2
    sstr2
    mpi
    @0
    @3
    @1
    @0
    @3
    wa
    #
    vx
    cA
    cB
    @4
    vx
    cv
    #
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    @4
    @6
    wa
    @5
    cB
    wceq
    #
    wn
    #
    @7
    @0
    @3
    @6
    @9
    @0
    @6
    @3
    @9
    @0
    @6
    @3
    @9
    wi
    @0
    @6
    wa
    @8
    @3
    @6
    @8
    cB
    cA
    wcel
    #
    @0
    @3
    wn
    #
    @8
    @6
    @10
    @5
    cB
    cA
    eleq1
    biimpcd
    @0
    @10
    @11
    @0
    @10
    wa
    #
    @2
    cA
    wcel
    #
    @11
    @0
    @10
    @13
    cA
    cB
    limsuc
    biimpa
    @12
    @3
    @13
    @12
    cA
    word
    #
    @2
    word
    #
    @3
    @13
    wn
    wb
    @0
    @14
    @10
    cA
    limord
    #
    adantr
    @12
    cB
    word
    #
    @15
    @0
    @14
    @10
    @17
    @16
    cA
    cB
    ordelord
    sylan
    cB
    ordsuc
    sylib
    cA
    @2
    ordtri1
    syl2anc
    con2bid
    mpbid
    ex
    sylan9r
    con2d
    ex
    com23
    imp31
    @3
    @6
    @9
    @7
    wi
    @0
    @3
    @6
    wa
    #
    @7
    @8
    @18
    @7
    @8
    @18
    @5
    @2
    wcel
    @7
    @8
    wo
    cA
    @2
    @5
    ssel2
    @5
    cB
    vx
    vex
    elsuc
    sylib
    ord
    con1d
    adantll
    mpd
    ex
    ssrdv
    ex
    impbid2
end
