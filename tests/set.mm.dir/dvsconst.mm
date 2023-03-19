include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cres.mm"
include "cdv.mm"
include "co.mm"
include "cc0.mm"
include "wf.mm"
include "wss.mm"
include "cdm.mm"
include "wceq.mm"
include "fconst6g.mm"
include "anim2i.mm"
include "recnprss.mm"
include "c0ex.mm"
include "fconst.mm"
include "fdmi.mm"
include "syl6sseqr.mm"
include "adantr.mm"
include "dvconst.mm"
include "adantl.mm"
include "dmeqd.mm"
include "sseqtr4d.mm"
include "ssid.mm"
include "jctil.mm"
include "dvres3.mm"
include "syl2anc.mm"
include "xpssres.mm"
include "syl.mm"
include "oveq2d.mm"
include "reseq1d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem dvsconst
  let cA: class A
  let cS: class S


  assert |- ( ( S e. { RR , CC } /\ A e. CC ) -> ( S _D ( S X. { A } ) ) = ( S X. { 0 } ) )

  proof
    cS
    cr
    cc
    cpr
    wcel
    #
    cA
    cc
    wcel
    #
    wa
    #
    cS
    cc
    cA
    csn
    #
    cxp
    #
    cS
    cres
    #
    cdv
    co
    #
    cc
    @4
    cdv
    co
    #
    cS
    cres
    #
    cS
    cS
    @3
    cxp
    #
    cdv
    co
    #
    cS
    cc0
    csn
    #
    cxp
    #
    @2
    @0
    cc
    cc
    @4
    wf
    #
    wa
    cc
    cc
    wss
    #
    cS
    @7
    cdm
    #
    wss
    #
    wa
    @6
    @8
    wceq
    @1
    @13
    @0
    cc
    cA
    cc
    fconst6g
    anim2i
    @2
    @16
    @14
    @2
    cS
    cc
    @11
    cxp
    #
    cdm
    #
    @15
    @0
    cS
    @18
    wss
    @1
    @0
    cS
    cc
    @18
    cS
    recnprss
    #
    cc
    @11
    @17
    cc
    cc0
    c0ex
    fconst
    fdmi
    syl6sseqr
    adantr
    @2
    @7
    @17
    @1
    @7
    @17
    wceq
    @0
    cA
    dvconst
    adantl
    #
    dmeqd
    sseqtr4d
    cc
    ssid
    jctil
    cc
    cS
    @4
    dvres3
    syl2anc
    @0
    @6
    @10
    wceq
    @1
    @0
    @5
    @9
    cS
    cdv
    @0
    cS
    cc
    wss
    #
    @5
    @9
    wceq
    @19
    cc
    @3
    cS
    xpssres
    syl
    oveq2d
    adantr
    @2
    @8
    @17
    cS
    cres
    #
    @12
    @2
    @7
    @17
    cS
    @20
    reseq1d
    @0
    @22
    @12
    wceq
    #
    @1
    @0
    @21
    @23
    @19
    cc
    @11
    cS
    xpssres
    syl
    adantr
    eqtrd
    3eqtr3d
end
