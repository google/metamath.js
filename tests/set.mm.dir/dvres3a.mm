include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "wf.mm"
include "wa.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "wceq.mm"
include "cres.mm"
include "wrel.mm"
include "wss.mm"
include "reldv.mm"
include "cin.mm"
include "recnprss.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "inss2.mm"
include "fssres.mm"
include "sylancl.mm"
include "rescom.mm"
include "resres.mm"
include "eqtri.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "reseq1d.mm"
include "syl5eqr.mm"
include "feq1d.mm"
include "mpbid.mm"
include "inss1.mm"
include "a1i.mm"
include "dvbss.mm"
include "dmres.mm"
include "simprr.mm"
include "ineq2d.mm"
include "syl5eq.mm"
include "sseqtr4d.mm"
include "relssres.mm"
include "sylancr.mm"
include "wfun.mm"
include "dvfg.mm"
include "ffun.mm"
include "syl.mm"
include "ssid.mm"
include "ctopon.mm"
include "cfv.mm"
include "cnfldtopon.mm"
include "simprl.mm"
include "toponss.mm"
include "dvres2.mm"
include "syl22anc.mm"
include "funssres.mm"
include "syl2anc.mm"
include "eqtr3d.mm"

theorem dvres3a
  let cA: class A
  let cS: class S
  let cF: class F
  let cJ: class J
  assume dvres3a.j: |- J = ( TopOpen ` CCfld )


  assert |- ( ( ( S e. { RR , CC } /\ F : A --> CC ) /\ ( A e. J /\ dom ( CC _D F ) = A ) ) -> ( S _D ( F |` S ) ) = ( ( CC _D F ) |` S ) )

  proof
    cS
    cr
    cc
    cpr
    wcel
    #
    cA
    cc
    cF
    wf
    #
    wa
    #
    cA
    cJ
    wcel
    #
    cc
    cF
    cdv
    co
    #
    cdm
    #
    cA
    wceq
    #
    wa
    #
    wa
    #
    cS
    cF
    cS
    cres
    #
    cdv
    co
    #
    @4
    cS
    cres
    #
    cdm
    #
    cres
    #
    @10
    @11
    @8
    @10
    wrel
    @10
    cdm
    #
    @12
    wss
    @13
    @10
    wceq
    cS
    @9
    reldv
    @8
    @14
    cS
    cA
    cin
    #
    @12
    @8
    @15
    cS
    @9
    @0
    cS
    cc
    wss
    #
    @1
    @7
    cS
    recnprss
    ad2antrr
    #
    @8
    @15
    cc
    cF
    @15
    cres
    #
    wf
    #
    @15
    cc
    @9
    wf
    @8
    @1
    @15
    cA
    wss
    @19
    @0
    @1
    @7
    simplr
    #
    cS
    cA
    inss2
    cA
    cc
    @15
    cF
    fssres
    sylancl
    @8
    @15
    cc
    @18
    @9
    @8
    @18
    cF
    cA
    cres
    #
    cS
    cres
    #
    @9
    @22
    @9
    cA
    cres
    @18
    cF
    cA
    cS
    rescom
    cF
    cS
    cA
    resres
    eqtri
    @8
    @21
    cF
    cS
    @8
    @1
    cF
    cA
    wfn
    @21
    cF
    wceq
    @20
    cA
    cc
    cF
    ffn
    cA
    cF
    fnresdm
    3syl
    reseq1d
    syl5eqr
    feq1d
    mpbid
    @15
    cS
    wss
    @8
    cS
    cA
    inss1
    a1i
    dvbss
    @8
    @12
    cS
    @5
    cin
    @15
    @4
    cS
    dmres
    @8
    @5
    cA
    cS
    @2
    @3
    @6
    simprr
    ineq2d
    syl5eq
    sseqtr4d
    @10
    @12
    relssres
    sylancr
    @8
    @10
    wfun
    #
    @11
    @10
    wss
    #
    @13
    @11
    wceq
    @8
    @14
    cc
    @10
    wf
    #
    @23
    @0
    @25
    @1
    @7
    cS
    @9
    dvfg
    ad2antrr
    @14
    cc
    @10
    ffun
    syl
    @8
    cc
    cc
    wss
    #
    @1
    cA
    cc
    wss
    #
    @16
    @24
    @26
    @8
    cc
    ssid
    a1i
    @20
    @8
    cJ
    cc
    ctopon
    cfv
    wcel
    @3
    @27
    cJ
    dvres3a.j
    cnfldtopon
    @2
    @3
    @6
    simprl
    cA
    cJ
    cc
    toponss
    sylancr
    @17
    cA
    cS
    cc
    cF
    dvres2
    syl22anc
    @10
    @11
    funssres
    syl2anc
    eqtr3d
end
