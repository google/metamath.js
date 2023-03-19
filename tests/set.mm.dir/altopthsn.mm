include "caltop.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wa.mm"
include "df-altop.mm"
include "eqeq12i.mm"
include "wo.mm"
include "snex.mm"
include "prex.mm"
include "preq12b.mm"
include "simpl.mm"
include "wss.mm"
include "snsspr1.mm"
include "sseq2.mm"
include "mpbii.mm"
include "adantl.mm"
include "mpbiri.mm"
include "adantr.mm"
include "eqssd.mm"
include "jaoi.mm"
include "sylbi.mm"
include "cun.mm"
include "uneq1.mm"
include "df-pr.mm"
include "3eqtr4g.mm"
include "preq2d.mm"
include "preq1.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "biimpd.mm"
include "preqr2.mm"
include "syl.mm"
include "syl6com.mm"
include "jcai.mm"
include "preq2.mm"
include "sylan9eq.mm"
include "impbii.mm"
include "bitri.mm"

theorem altopthsn
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( << A , B >> = << C , D >> <-> ( { A } = { C } /\ { B } = { D } ) )

  proof
    cA
    cB
    caltop
    #
    cC
    cD
    caltop
    #
    wceq
    cA
    csn
    #
    cA
    cB
    csn
    #
    cpr
    #
    cpr
    #
    cC
    csn
    #
    cC
    cD
    csn
    #
    cpr
    #
    cpr
    #
    wceq
    #
    @2
    @6
    wceq
    #
    @3
    @7
    wceq
    #
    wa
    #
    @0
    @5
    @1
    @9
    cA
    cB
    df-altop
    cC
    cD
    df-altop
    eqeq12i
    @10
    @13
    @10
    @11
    @12
    @10
    @11
    @4
    @8
    wceq
    #
    wa
    #
    @2
    @8
    wceq
    #
    @4
    @6
    wceq
    #
    wa
    #
    wo
    @11
    @2
    @4
    @6
    @8
    cA
    snex
    cA
    @3
    prex
    cC
    snex
    cC
    @7
    prex
    #
    preq12b
    @15
    @11
    @18
    @11
    @14
    simpl
    @18
    @2
    @6
    @17
    @2
    @6
    wss
    #
    @16
    @17
    @2
    @4
    wss
    @20
    cA
    @3
    snsspr1
    @4
    @6
    @2
    sseq2
    mpbii
    adantl
    @16
    @6
    @2
    wss
    #
    @17
    @16
    @21
    @6
    @8
    wss
    cC
    @7
    snsspr1
    @2
    @8
    @6
    sseq2
    mpbiri
    adantr
    eqssd
    jaoi
    sylbi
    @11
    @10
    @6
    cC
    @3
    cpr
    #
    cpr
    #
    @9
    wceq
    #
    @12
    @11
    @10
    @24
    @11
    @5
    @23
    @9
    @11
    @5
    @2
    @22
    cpr
    @23
    @11
    @4
    @22
    @2
    @11
    @2
    @3
    csn
    #
    cun
    @6
    @25
    cun
    @4
    @22
    @2
    @6
    @25
    uneq1
    cA
    @3
    df-pr
    cC
    @3
    df-pr
    3eqtr4g
    preq2d
    @2
    @6
    @22
    preq1
    eqtrd
    #
    eqeq1d
    biimpd
    @24
    @22
    @8
    wceq
    @12
    @22
    @8
    @6
    cC
    @3
    prex
    @19
    preqr2
    @3
    @7
    cC
    cB
    snex
    cD
    snex
    preqr2
    syl
    syl6com
    jcai
    @11
    @12
    @5
    @23
    @9
    @26
    @12
    @22
    @8
    @6
    @3
    @7
    cC
    preq2
    preq2d
    sylan9eq
    impbii
    bitri
end
