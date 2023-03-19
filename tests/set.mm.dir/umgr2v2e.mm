include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cumgr.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "cc0.mm"
include "cpr.mm"
include "cop.mm"
include "c1.mm"
include "cvv.mm"
include "c0ex.mm"
include "1ex.mm"
include "pm3.2i.mm"
include "prex.mm"
include "0ne1.mm"
include "a1i.mm"
include "fprg.mm"
include "mp3an12i.mm"
include "csn.mm"
include "dfsn2.mm"
include "prelpwi.mm"
include "3adant1.mm"
include "umgr2v2evtx.mm"
include "3ad2ant1.mm"
include "pweqd.mm"
include "eleqtrrd.mm"
include "adantr.mm"
include "wi.mm"
include "hashprg.mm"
include "biimpd.mm"
include "imp.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "snssd.mm"
include "syl5eqssr.mm"
include "fssd.mm"
include "ffdmd.mm"
include "umgr2v2eiedg.mm"
include "dmeqd.mm"
include "feq12d.mm"
include "mpbird.mm"
include "wb.mm"
include "opex.mm"
include "eqeltri.mm"
include "eqid.mm"
include "isumgrs.mm"
include "mp1i.mm"

theorem umgr2v2e
  let cA: class A
  let cB: class B
  let cG: class G
  let cV: class V
  let cW: class W
  let ve: setvar e
  assume umgr2v2evtx.g: |- G = <. V , { <. 0 , { A , B } >. , <. 1 , { A , B } >. } >.


  assert |- ( ( ( V e. W /\ A e. V /\ B e. V ) /\ A =/= B ) -> G e. UMGraph )

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
    cumgr
    wcel
    #
    cG
    ciedg
    cfv
    #
    cdm
    #
    ve
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    ve
    cG
    cvtx
    cfv
    #
    cpw
    #
    crab
    #
    @7
    wf
    #
    @5
    @15
    cc0
    cA
    cB
    cpr
    #
    cop
    c1
    @16
    cop
    cpr
    #
    cdm
    #
    @14
    @17
    wf
    @5
    cc0
    c1
    cpr
    #
    @14
    @17
    @5
    @19
    @16
    @16
    cpr
    #
    @14
    @17
    cc0
    cvv
    wcel
    #
    c1
    cvv
    wcel
    #
    wa
    @16
    cvv
    wcel
    #
    @23
    wa
    @5
    cc0
    c1
    wne
    #
    @19
    @20
    @17
    wf
    @21
    @22
    c0ex
    1ex
    pm3.2i
    @23
    @23
    cA
    cB
    prex
    #
    @25
    pm3.2i
    @24
    @5
    0ne1
    a1i
    cc0
    c1
    @16
    @16
    cvv
    cvv
    cvv
    cvv
    fprg
    mp3an12i
    @5
    @20
    @16
    csn
    @14
    @16
    dfsn2
    @5
    @16
    @14
    @5
    @16
    @13
    wcel
    #
    @16
    chash
    cfv
    #
    c2
    wceq
    #
    @16
    @14
    wcel
    @3
    @26
    @4
    @3
    @16
    cV
    cpw
    #
    @13
    @1
    @2
    @16
    @29
    wcel
    @0
    cA
    cB
    cV
    prelpwi
    3adant1
    @3
    @12
    cV
    @0
    @1
    @12
    cV
    wceq
    @2
    cA
    cB
    cG
    cV
    cW
    umgr2v2evtx.g
    umgr2v2evtx
    3ad2ant1
    pweqd
    eleqtrrd
    adantr
    @3
    @4
    @28
    @1
    @2
    @4
    @28
    wi
    @0
    @1
    @2
    wa
    @4
    @28
    cA
    cB
    cV
    cV
    hashprg
    biimpd
    3adant1
    imp
    @11
    @28
    ve
    @16
    @13
    @9
    @16
    wceq
    @10
    @27
    c2
    @9
    @16
    chash
    fveq2
    eqeq1d
    elrab
    sylanbrc
    snssd
    syl5eqssr
    fssd
    ffdmd
    @5
    @8
    @18
    @14
    @7
    @17
    @3
    @7
    @17
    wceq
    @4
    cA
    cB
    cG
    cV
    cW
    umgr2v2evtx.g
    umgr2v2eiedg
    adantr
    #
    @5
    @7
    @17
    @30
    dmeqd
    feq12d
    mpbird
    cG
    cvv
    wcel
    @6
    @15
    wb
    @5
    cG
    cV
    @17
    cop
    cvv
    umgr2v2evtx.g
    cV
    @17
    opex
    eqeltri
    ve
    cvv
    @7
    cG
    @12
    @12
    eqid
    @7
    eqid
    isumgrs
    mp1i
    mpbird
end
