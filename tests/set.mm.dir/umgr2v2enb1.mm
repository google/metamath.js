include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "cpr.mm"
include "cedg.mm"
include "cfv.mm"
include "cvtx.mm"
include "crab.mm"
include "csn.mm"
include "cumgr.mm"
include "wceq.mm"
include "umgr2v2e.mm"
include "umgr2v2evtxel.mm"
include "3adant3.mm"
include "adantr.mm"
include "eqid.mm"
include "nbumgrvtx.mm"
include "syl2anc.mm"
include "wb.mm"
include "wal.mm"
include "umgr2v2eedg.mm"
include "eleq2d.mm"
include "prex.mm"
include "elsn.mm"
include "syl6bb.mm"
include "simpr.mm"
include "simpll3.mm"
include "preq2b.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "wi.mm"
include "umgr2v2evtx.mm"
include "3ad2ant1.mm"
include "eleq12.mm"
include "exbiri.mm"
include "com13.mm"
include "3ad2ant3.mm"
include "mpd.mm"
include "pm4.71rd.mm"
include "bitr4d.mm"
include "alrimiv.mm"
include "rabeqsn.mm"
include "sylibr.mm"
include "eqtrd.mm"

theorem umgr2v2enb1
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vx: setvar x
  assume umgr2v2evtx.g: |- G = <. V , { <. 0 , { A , B } >. , <. 1 , { A , B } >. } >.


  assert |- ( ( ( V e. W /\ A e. V /\ B e. V ) /\ A =/= B ) -> ( G NeighbVtx A ) = { B } )

  proof
    cV
    cW
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cA
    cB
    wne
    #
    wa
    #
    cG
    cA
    cnbgr
    co
    #
    cA
    vx
    cv
    #
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    vx
    cG
    cvtx
    cfv
    #
    crab
    #
    cB
    csn
    #
    @5
    cG
    cumgr
    wcel
    cA
    @11
    wcel
    #
    @6
    @12
    wceq
    cA
    cB
    cG
    cV
    cW
    umgr2v2evtx.g
    umgr2v2e
    @3
    @14
    @4
    @0
    @1
    @14
    @2
    cA
    cB
    cG
    cV
    cW
    umgr2v2evtx.g
    umgr2v2evtxel
    3adant3
    adantr
    vx
    @9
    cG
    cA
    @11
    @11
    eqid
    @9
    eqid
    nbumgrvtx
    syl2anc
    @5
    @7
    @11
    wcel
    #
    @10
    wa
    #
    @7
    cB
    wceq
    #
    wb
    #
    vx
    wal
    @12
    @13
    wceq
    @5
    @18
    vx
    @5
    @16
    @15
    @17
    wa
    @17
    @5
    @15
    @10
    @17
    @5
    @15
    wa
    #
    @10
    @8
    cA
    cB
    cpr
    #
    wceq
    #
    @17
    @19
    @10
    @8
    @20
    csn
    #
    wcel
    #
    @21
    @5
    @10
    @23
    wb
    #
    @15
    @3
    @24
    @4
    @3
    @9
    @22
    @8
    cA
    cB
    cG
    cV
    cW
    umgr2v2evtx.g
    umgr2v2eedg
    eleq2d
    adantr
    adantr
    @8
    @20
    cA
    @7
    prex
    elsn
    syl6bb
    @19
    @7
    cB
    cA
    @11
    cV
    @5
    @15
    simpr
    @0
    @1
    @2
    @4
    @15
    simpll3
    preq2b
    bitrd
    pm5.32da
    @5
    @17
    @15
    @3
    @17
    @15
    wi
    #
    @4
    @3
    @11
    cV
    wceq
    #
    @25
    @0
    @1
    @26
    @2
    cA
    cB
    cG
    cV
    cW
    umgr2v2evtx.g
    umgr2v2evtx
    3ad2ant1
    @2
    @0
    @26
    @25
    wi
    @1
    @17
    @26
    @2
    @15
    @17
    @26
    @15
    @2
    @7
    cB
    @11
    cV
    eleq12
    exbiri
    com13
    3ad2ant3
    mpd
    adantr
    pm4.71rd
    bitr4d
    alrimiv
    @10
    vx
    @11
    cB
    rabeqsn
    sylibr
    eqtrd
end
