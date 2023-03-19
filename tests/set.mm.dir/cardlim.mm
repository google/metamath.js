include "com.mm"
include "ccrd.mm"
include "cfv.mm"
include "wss.mm"
include "wlim.mm"
include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "con0.mm"
include "wrex.mm"
include "wn.mm"
include "wcel.mm"
include "wa.mm"
include "cen.mm"
include "wbr.mm"
include "wi.mm"
include "sseq2.mm"
include "biimpd.mm"
include "wb.mm"
include "limom.mm"
include "limsssuc.mm"
include "ax-mp.mm"
include "infensuc.mm"
include "ex.mm"
include "syl5bir.mm"
include "sylan9r.mm"
include "breq2.mm"
include "adantl.mm"
include "sylibrd.mm"
include "com3r.mm"
include "imp.mm"
include "vex.mm"
include "sucid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "cardidm.mm"
include "syl6eleqr.mm"
include "cardne.mm"
include "syl.mm"
include "a1i.mm"
include "pm2.65d.mm"
include "nrexdv.mm"
include "c0.mm"
include "wo.mm"
include "peano1.mm"
include "ssel.mm"
include "mpi.mm"
include "n0i.mm"
include "w3o.mm"
include "word.mm"
include "cardon.mm"
include "onordi.mm"
include "ordzsl.mm"
include "mpbi.mm"
include "3orass.mm"
include "ori.mm"
include "3syl.mm"
include "ord.mm"
include "mpd.mm"
include "limomss.mm"
include "impbii.mm"

theorem cardlim
  let cA: class A
  let vx: setvar x


  assert |- ( _om C_ ( card ` A ) <-> Lim ( card ` A ) )

  proof
    com
    cA
    ccrd
    cfv
    #
    wss
    #
    @0
    wlim
    #
    @1
    @0
    vx
    cv
    #
    csuc
    #
    wceq
    #
    vx
    con0
    wrex
    #
    wn
    @2
    @1
    @5
    vx
    con0
    @1
    @3
    con0
    wcel
    #
    wa
    #
    @5
    @3
    @0
    cen
    wbr
    #
    @1
    @7
    @5
    @9
    wi
    @7
    @5
    @1
    @9
    @7
    @5
    @1
    @9
    wi
    @7
    @5
    wa
    @1
    @3
    @4
    cen
    wbr
    #
    @9
    @5
    @1
    com
    @4
    wss
    #
    @7
    @10
    @5
    @1
    @11
    @0
    @4
    com
    sseq2
    biimpd
    @11
    com
    @3
    wss
    #
    @7
    @10
    com
    wlim
    @12
    @11
    wb
    limom
    com
    @3
    limsssuc
    ax-mp
    @7
    @12
    @10
    @3
    infensuc
    ex
    syl5bir
    sylan9r
    @5
    @9
    @10
    wb
    @7
    @0
    @4
    @3
    cen
    breq2
    adantl
    sylibrd
    ex
    com3r
    imp
    @5
    @9
    wn
    #
    wi
    @8
    @5
    @3
    @0
    ccrd
    cfv
    #
    wcel
    @13
    @5
    @3
    @0
    @14
    @5
    @3
    @0
    wcel
    @3
    @4
    wcel
    @3
    vx
    vex
    sucid
    @0
    @4
    @3
    eleq2
    mpbiri
    cA
    cardidm
    syl6eleqr
    @3
    @0
    cardne
    syl
    a1i
    pm2.65d
    nrexdv
    @1
    @6
    @2
    @1
    c0
    @0
    wcel
    #
    @0
    c0
    wceq
    #
    wn
    @6
    @2
    wo
    #
    @1
    c0
    com
    wcel
    @15
    peano1
    com
    @0
    c0
    ssel
    mpi
    @0
    c0
    n0i
    @16
    @17
    @16
    @6
    @2
    w3o
    #
    @16
    @17
    wo
    @0
    word
    @18
    @0
    cA
    cardon
    onordi
    vx
    @0
    ordzsl
    mpbi
    @16
    @6
    @2
    3orass
    mpbi
    ori
    3syl
    ord
    mpd
    @0
    limomss
    impbii
end
