include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "wf.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "w3a.mm"
include "simpr.mm"
include "prid1g.mm"
include "ad2antrr.mm"
include "ffvelrnd.mm"
include "prid2g.mm"
include "ad2antlr.mm"
include "wfn.mm"
include "ffn.mm"
include "adantl.mm"
include "wb.mm"
include "fnpr2g.mm"
include "adantr.mm"
include "mpbid.mm"
include "3jca.mm"
include "cxp.mm"
include "wss.mm"
include "biimpar.mm"
include "3ad2antr3.mm"
include "simpr3.mm"
include "simpr1.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "simpr2.mm"
include "jca.mm"
include "opex.mm"
include "prss.mm"
include "sylib.mm"
include "eqsstrd.mm"
include "dff2.mm"
include "sylanbrc.mm"
include "impbida.mm"

theorem fpr2g
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( F : { A , B } --> C <-> ( ( F ` A ) e. C /\ ( F ` B ) e. C /\ F = { <. A , ( F ` A ) >. , <. B , ( F ` B ) >. } ) ) )

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
    cC
    cF
    wf
    #
    cA
    cF
    cfv
    #
    cC
    wcel
    #
    cB
    cF
    cfv
    #
    cC
    wcel
    #
    cF
    cA
    @5
    cop
    #
    cB
    @7
    cop
    #
    cpr
    #
    wceq
    #
    w3a
    #
    @2
    @4
    wa
    #
    @6
    @8
    @12
    @14
    @3
    cC
    cA
    cF
    @2
    @4
    simpr
    #
    @0
    cA
    @3
    wcel
    #
    @1
    @4
    cA
    cB
    cV
    prid1g
    #
    ad2antrr
    ffvelrnd
    @14
    @3
    cC
    cB
    cF
    @15
    @1
    cB
    @3
    wcel
    #
    @0
    @4
    cA
    cB
    cW
    prid2g
    #
    ad2antlr
    ffvelrnd
    @14
    cF
    @3
    wfn
    #
    @12
    @4
    @20
    @2
    @3
    cC
    cF
    ffn
    adantl
    @2
    @20
    @12
    wb
    @4
    cA
    cB
    cF
    cV
    cW
    fnpr2g
    #
    adantr
    mpbid
    3jca
    @2
    @13
    wa
    #
    @20
    cF
    @3
    cC
    cxp
    #
    wss
    @4
    @2
    @6
    @12
    @20
    @8
    @2
    @20
    @12
    @21
    biimpar
    3ad2antr3
    @22
    cF
    @11
    @23
    @2
    @6
    @8
    @12
    simpr3
    @22
    @9
    @23
    wcel
    #
    @10
    @23
    wcel
    #
    wa
    @11
    @23
    wss
    @22
    @24
    @25
    @22
    @16
    @6
    @24
    @0
    @16
    @1
    @13
    @17
    ad2antrr
    @2
    @6
    @8
    @12
    simpr1
    cA
    @5
    @3
    cC
    opelxpi
    syl2anc
    @22
    @18
    @8
    @25
    @1
    @18
    @0
    @13
    @19
    ad2antlr
    @2
    @6
    @8
    @12
    simpr2
    cB
    @7
    @3
    cC
    opelxpi
    syl2anc
    jca
    @9
    @10
    @23
    cA
    @5
    opex
    cB
    @7
    opex
    prss
    sylib
    eqsstrd
    @3
    cC
    cF
    dff2
    sylanbrc
    impbida
end
