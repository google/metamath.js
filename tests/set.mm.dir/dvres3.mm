include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "wf.mm"
include "wa.mm"
include "wss.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "cres.mm"
include "wrel.mm"
include "wceq.mm"
include "reldv.mm"
include "recnprss.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprr.mm"
include "ssid.mm"
include "a1i.mm"
include "simprl.mm"
include "dvbss.mm"
include "sstrd.mm"
include "fssresd.mm"
include "ssdmres.mm"
include "sylib.mm"
include "sseqtr4d.mm"
include "relssres.mm"
include "sylancr.mm"
include "wfun.mm"
include "dvfg.mm"
include "ffun.mm"
include "syl.mm"
include "dvres2.mm"
include "syl22anc.mm"
include "funssres.mm"
include "syl2anc.mm"
include "eqtr3d.mm"

theorem dvres3
  let cA: class A
  let cS: class S
  let cF: class F


  assert |- ( ( ( S e. { RR , CC } /\ F : A --> CC ) /\ ( A C_ CC /\ S C_ dom ( CC _D F ) ) ) -> ( S _D ( F |` S ) ) = ( ( CC _D F ) |` S ) )

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
    cc
    wss
    #
    cS
    cc
    cF
    cdv
    co
    #
    cdm
    #
    wss
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
    @12
    @8
    cS
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
    cA
    cc
    cS
    cF
    @0
    @1
    @7
    simplr
    #
    @8
    cS
    @5
    cA
    @2
    @3
    @6
    simprr
    #
    @8
    cA
    cc
    cF
    cc
    cc
    wss
    #
    @8
    cc
    ssid
    a1i
    #
    @17
    @2
    @3
    @6
    simprl
    #
    dvbss
    sstrd
    fssresd
    cS
    cS
    wss
    @8
    cS
    ssid
    a1i
    dvbss
    @8
    @6
    @12
    cS
    wceq
    @18
    cS
    @4
    ssdmres
    sylib
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
    @22
    @0
    @24
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
    @19
    @1
    @3
    @15
    @23
    @20
    @17
    @21
    @16
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
