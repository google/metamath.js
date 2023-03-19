include "csur.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "cdm.mm"
include "wss.mm"
include "wn.mm"
include "wceq.mm"
include "nosepne.mm"
include "neneqd.mm"
include "wa.mm"
include "c0.mm"
include "wi.mm"
include "word.mm"
include "nodmord.mm"
include "3ad2ant1.mm"
include "ordn2lp.mm"
include "syl.mm"
include "imnan.mm"
include "sylibr.mm"
include "imp.mm"
include "ndmfv.mm"
include "nosepeq.mm"
include "simpl1.mm"
include "ordirr.mm"
include "3syl.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "wfun.mm"
include "crn.mm"
include "wb.mm"
include "simpl2.mm"
include "nofun.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "nosgnn0.mm"
include "norn.mm"
include "sseld.mm"
include "mtoi.mm"
include "funeldmb.mm"
include "syl2anc.mm"
include "necon2bbid.mm"
include "3ad2ant2.mm"
include "ordtr1.mm"
include "expdimp.mm"
include "con3d.mm"
include "sylbid.mm"
include "mpd.mm"
include "eqtr4d.mm"
include "mtand.mm"
include "nosepon.mm"
include "nodmon.mm"
include "ontri1.mm"
include "mpbird.mm"

theorem nosepssdm
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. No /\ B e. No /\ A =/= B ) -> |^| { x e. On | ( A ` x ) =/= ( B ` x ) } C_ dom A )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    vx
    cv
    #
    cA
    cfv
    @4
    cB
    cfv
    wne
    vx
    con0
    crab
    cint
    #
    cA
    cdm
    #
    wss
    #
    @6
    @5
    wcel
    #
    wn
    #
    @3
    @8
    @5
    cA
    cfv
    #
    @5
    cB
    cfv
    #
    wceq
    @3
    @10
    @11
    vx
    cA
    cB
    nosepne
    neneqd
    @3
    @8
    wa
    #
    @10
    c0
    @11
    @12
    @5
    @6
    wcel
    #
    wn
    #
    @10
    c0
    wceq
    @3
    @8
    @14
    @3
    @8
    @13
    wa
    wn
    #
    @8
    @14
    wi
    @3
    @6
    word
    #
    @15
    @0
    @1
    @16
    @2
    cA
    nodmord
    #
    3ad2ant1
    @6
    @5
    ordn2lp
    syl
    @8
    @13
    imnan
    sylibr
    imp
    @5
    cA
    ndmfv
    syl
    @12
    @5
    cB
    cdm
    #
    wcel
    #
    wn
    #
    @11
    c0
    wceq
    @12
    @6
    cA
    cfv
    #
    @6
    cB
    cfv
    #
    wceq
    #
    @20
    vx
    cA
    cB
    @6
    nosepeq
    @12
    @23
    @22
    c0
    wceq
    #
    @20
    @12
    @23
    c0
    @22
    wceq
    @24
    @12
    @21
    c0
    @22
    @12
    @16
    @6
    @6
    wcel
    wn
    @21
    c0
    wceq
    @12
    @0
    @16
    @0
    @1
    @2
    @8
    simpl1
    @17
    syl
    @6
    ordirr
    @6
    cA
    ndmfv
    3syl
    eqeq1d
    c0
    @22
    eqcom
    syl6bb
    @12
    @24
    @6
    @18
    wcel
    #
    wn
    @20
    @12
    @25
    @22
    c0
    @12
    cB
    wfun
    #
    c0
    cB
    crn
    #
    wcel
    #
    wn
    @25
    @22
    c0
    wne
    wb
    @12
    @1
    @26
    @0
    @1
    @2
    @8
    simpl2
    #
    cB
    nofun
    syl
    @12
    @28
    c0
    c1o
    c2o
    cpr
    #
    wcel
    nosgnn0
    @12
    @27
    @30
    c0
    @12
    @1
    @27
    @30
    wss
    @29
    cB
    norn
    syl
    sseld
    mtoi
    @6
    cB
    funeldmb
    syl2anc
    necon2bbid
    @12
    @19
    @25
    @3
    @8
    @19
    @25
    @3
    @18
    word
    #
    @8
    @19
    wa
    @25
    wi
    @1
    @0
    @31
    @2
    cB
    nodmord
    3ad2ant2
    @6
    @5
    @18
    ordtr1
    syl
    expdimp
    con3d
    sylbid
    sylbid
    mpd
    @5
    cB
    ndmfv
    syl
    eqtr4d
    mtand
    @3
    @5
    con0
    wcel
    @6
    con0
    wcel
    #
    @7
    @9
    wb
    vx
    cA
    cB
    nosepon
    @0
    @1
    @32
    @2
    cA
    nodmon
    3ad2ant1
    @5
    @6
    ontri1
    syl2anc
    mpbird
end
