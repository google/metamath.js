include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "cop.mm"
include "wf1o.mm"
include "wceq.mm"
include "csn.mm"
include "f1osng.mm"
include "anidms.mm"
include "ad2antrr.mm"
include "wb.mm"
include "dfsn2.mm"
include "opeq2.mm"
include "opeq1.mm"
include "preq12d.mm"
include "syl5eq.mm"
include "preq2.mm"
include "f1oeq123d.mm"
include "adantl.mm"
include "mpbid.mm"
include "wne.mm"
include "wfn.mm"
include "ccnv.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "fnprg.mm"
include "syl221anc.mm"
include "cun.mm"
include "cnvsng.mm"
include "ancoms.mm"
include "uneq12d.mm"
include "uncom.mm"
include "syl6eq.mm"
include "adantr.mm"
include "df-pr.mm"
include "cnveqi.mm"
include "cnvun.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "dff1o4.mm"
include "sylanbrc.mm"
include "pm2.61dane.mm"

theorem f1oprswap
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> { <. A , B >. , <. B , A >. } : { A , B } -1-1-onto-> { A , B } )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    cB
    cpr
    #
    @3
    cA
    cB
    cop
    #
    cB
    cA
    cop
    #
    cpr
    #
    wf1o
    #
    cA
    cB
    @2
    cA
    cB
    wceq
    #
    wa
    cA
    csn
    #
    @9
    cA
    cA
    cop
    #
    csn
    #
    wf1o
    #
    @7
    @0
    @12
    @1
    @8
    @0
    @12
    cA
    cA
    cV
    cV
    f1osng
    anidms
    ad2antrr
    @8
    @12
    @7
    wb
    @2
    @8
    @9
    @3
    @9
    @3
    @11
    @6
    @8
    @11
    @10
    @10
    cpr
    @6
    @10
    dfsn2
    @8
    @10
    @4
    @10
    @5
    cA
    cB
    cA
    opeq2
    cA
    cB
    cA
    opeq1
    preq12d
    syl5eq
    @8
    @9
    cA
    cA
    cpr
    @3
    cA
    dfsn2
    cA
    cB
    cA
    preq2
    syl5eq
    #
    @13
    f1oeq123d
    adantl
    mpbid
    @2
    cA
    cB
    wne
    #
    wa
    #
    @6
    @3
    wfn
    #
    @6
    ccnv
    #
    @3
    wfn
    #
    @7
    @15
    @0
    @1
    @1
    @0
    @14
    @16
    @0
    @1
    @14
    simpll
    #
    @0
    @1
    @14
    simplr
    #
    @20
    @19
    @2
    @14
    simpr
    cA
    cB
    cB
    cA
    cV
    cW
    cW
    cV
    fnprg
    syl221anc
    #
    @15
    @18
    @16
    @21
    @15
    @3
    @17
    @6
    @15
    @4
    csn
    #
    ccnv
    #
    @5
    csn
    #
    ccnv
    #
    cun
    #
    @22
    @24
    cun
    #
    @17
    @6
    @2
    @26
    @27
    wceq
    @14
    @2
    @26
    @24
    @22
    cun
    @27
    @2
    @23
    @24
    @25
    @22
    cA
    cB
    cV
    cW
    cnvsng
    @1
    @0
    @25
    @22
    wceq
    cB
    cA
    cW
    cV
    cnvsng
    ancoms
    uneq12d
    @24
    @22
    uncom
    syl6eq
    adantr
    @17
    @27
    ccnv
    @26
    @6
    @27
    @4
    @5
    df-pr
    #
    cnveqi
    @22
    @24
    cnvun
    eqtri
    @28
    3eqtr4g
    fneq1d
    mpbird
    @3
    @3
    @6
    dff1o4
    sylanbrc
    pm2.61dane
end
