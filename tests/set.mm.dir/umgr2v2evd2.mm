include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cv.mm"
include "ciedg.mm"
include "cdm.mm"
include "crab.mm"
include "chash.mm"
include "c2.mm"
include "cumgr.mm"
include "cvtx.mm"
include "wceq.mm"
include "umgr2v2e.mm"
include "umgr2v2evtxel.mm"
include "3adant3.mm"
include "adantr.mm"
include "eqid.mm"
include "vtxdumgrval.mm"
include "syl2anc.mm"
include "cc0.mm"
include "cpr.mm"
include "cop.mm"
include "c1.mm"
include "umgr2v2eiedg.mm"
include "dmeqd.mm"
include "prex.mm"
include "dmprop.mm"
include "syl6eq.mm"
include "fveq1d.mm"
include "eleq2d.mm"
include "rabeqbidv.mm"
include "fveq2d.mm"
include "wral.mm"
include "prid1g.mm"
include "0ne1.mm"
include "c0ex.mm"
include "fvpr1.mm"
include "ax-mp.mm"
include "syl6eleqr.mm"
include "1ex.mm"
include "fvpr2.mm"
include "fveq2.mm"
include "ralpr.mm"
include "sylanbrc.mm"
include "rabid2.mm"
include "sylibr.mm"
include "eqcomd.mm"
include "prhash2ex.mm"
include "3ad2ant2.mm"
include "eqtrd.mm"

theorem umgr2v2evd2
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vx: setvar x
  assume umgr2v2evtx.g: |- G = <. V , { <. 0 , { A , B } >. , <. 1 , { A , B } >. } >.


  assert |- ( ( ( V e. W /\ A e. V /\ B e. V ) /\ A =/= B ) -> ( ( VtxDeg ` G ) ` A ) = 2 )

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
    cA
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cA
    vx
    cv
    #
    cG
    ciedg
    cfv
    #
    cfv
    #
    wcel
    #
    vx
    @9
    cdm
    #
    crab
    #
    chash
    cfv
    #
    c2
    @5
    cG
    cumgr
    wcel
    cA
    cG
    cvtx
    cfv
    #
    wcel
    #
    @7
    @14
    wceq
    cA
    cB
    cG
    cV
    cW
    umgr2v2evtx.g
    umgr2v2e
    @3
    @16
    @4
    @0
    @1
    @16
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
    @12
    @6
    cA
    cG
    @9
    @15
    @15
    eqid
    @9
    eqid
    @12
    eqid
    @6
    eqid
    vtxdumgrval
    syl2anc
    @3
    @14
    c2
    wceq
    @4
    @3
    @14
    cA
    @8
    cc0
    cA
    cB
    cpr
    #
    cop
    c1
    @17
    cop
    cpr
    #
    cfv
    #
    wcel
    #
    vx
    cc0
    c1
    cpr
    #
    crab
    #
    chash
    cfv
    #
    c2
    @3
    @13
    @22
    chash
    @3
    @11
    @20
    vx
    @12
    @21
    @3
    @12
    @18
    cdm
    @21
    @3
    @9
    @18
    cA
    cB
    cG
    cV
    cW
    umgr2v2evtx.g
    umgr2v2eiedg
    #
    dmeqd
    cc0
    @17
    c1
    @17
    cA
    cB
    prex
    #
    @25
    dmprop
    syl6eq
    @3
    @10
    @19
    cA
    @3
    @8
    @9
    @18
    @24
    fveq1d
    eleq2d
    rabeqbidv
    fveq2d
    @1
    @0
    @23
    c2
    wceq
    @2
    @1
    @23
    @21
    chash
    cfv
    c2
    @1
    @22
    @21
    chash
    @1
    @21
    @22
    @1
    @20
    vx
    @21
    wral
    #
    @21
    @22
    wceq
    @1
    cA
    cc0
    @18
    cfv
    #
    wcel
    #
    cA
    c1
    @18
    cfv
    #
    wcel
    #
    @26
    @1
    cA
    @17
    @27
    cA
    cB
    cV
    prid1g
    #
    cc0
    c1
    wne
    #
    @27
    @17
    wceq
    0ne1
    cc0
    c1
    @17
    @17
    c0ex
    @25
    fvpr1
    ax-mp
    syl6eleqr
    @1
    cA
    @17
    @29
    @31
    @32
    @29
    @17
    wceq
    0ne1
    cc0
    c1
    @17
    @17
    1ex
    @25
    fvpr2
    ax-mp
    syl6eleqr
    @20
    @28
    @30
    vx
    cc0
    c1
    c0ex
    1ex
    @8
    cc0
    wceq
    @19
    @27
    cA
    @8
    cc0
    @18
    fveq2
    eleq2d
    @8
    c1
    wceq
    @19
    @29
    cA
    @8
    c1
    @18
    fveq2
    eleq2d
    ralpr
    sylanbrc
    @20
    vx
    @21
    rabid2
    sylibr
    eqcomd
    fveq2d
    prhash2ex
    syl6eq
    3ad2ant2
    eqtrd
    adantr
    eqtrd
end
