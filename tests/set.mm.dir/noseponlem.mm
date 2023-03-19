include "csur.mm"
include "wcel.mm"
include "cdm.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "con0.mm"
include "wrex.mm"
include "wceq.mm"
include "wral.mm"
include "wn.mm"
include "nodmon.mm"
include "3ad2ant1.mm"
include "c0.mm"
include "word.mm"
include "nodmord.mm"
include "ordirr.mm"
include "syl.mm"
include "ndmfv.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "nosgnn0.mm"
include "wf.mm"
include "elno3.mm"
include "simplbi.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "ffvelrnd.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "mtoi.mm"
include "neqned.mm"
include "necomd.mm"
include "eqnetrd.mm"
include "fveq2.mm"
include "neeq12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "df-ne.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "sylib.mm"

theorem noseponlem
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. No /\ B e. No /\ dom A e. dom B ) -> -. A. x e. On ( A ` x ) = ( B ` x ) )

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
    cdm
    #
    cB
    cdm
    #
    wcel
    #
    w3a
    #
    vx
    cv
    #
    cA
    cfv
    #
    @6
    cB
    cfv
    #
    wne
    #
    vx
    con0
    wrex
    #
    @7
    @8
    wceq
    #
    vx
    con0
    wral
    wn
    #
    @5
    @2
    con0
    wcel
    #
    @2
    cA
    cfv
    #
    @2
    cB
    cfv
    #
    wne
    #
    @10
    @0
    @1
    @13
    @4
    cA
    nodmon
    3ad2ant1
    @5
    @14
    c0
    @15
    @5
    @2
    @2
    wcel
    wn
    #
    @14
    c0
    wceq
    @0
    @1
    @17
    @4
    @0
    @2
    word
    @17
    cA
    nodmord
    @2
    ordirr
    syl
    3ad2ant1
    @2
    cA
    ndmfv
    syl
    @5
    @15
    c0
    @5
    @15
    c0
    @5
    @15
    c0
    wceq
    #
    c0
    c1o
    c2o
    cpr
    #
    wcel
    #
    nosgnn0
    @5
    @15
    @19
    wcel
    @18
    @20
    @5
    @3
    @19
    @2
    cB
    @1
    @0
    @3
    @19
    cB
    wf
    #
    @4
    @1
    @21
    @3
    con0
    wcel
    cB
    elno3
    simplbi
    3ad2ant2
    @0
    @1
    @4
    simp3
    ffvelrnd
    @15
    c0
    @19
    eleq1
    syl5ibcom
    mtoi
    neqned
    necomd
    eqnetrd
    @9
    @16
    vx
    @2
    con0
    @6
    @2
    wceq
    @7
    @14
    @8
    @15
    @6
    @2
    cA
    fveq2
    @6
    @2
    cB
    fveq2
    neeq12d
    rspcev
    syl2anc
    @10
    @11
    wn
    #
    vx
    con0
    wrex
    @12
    @9
    @22
    vx
    con0
    @7
    @8
    df-ne
    rexbii
    @11
    vx
    con0
    rexnal
    bitri
    sylib
end
