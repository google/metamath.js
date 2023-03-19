include "cn0.mm"
include "wcel.mm"
include "cc.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "elnn0.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "cfv.mm"
include "cuz.mm"
include "seqp1.mm"
include "nnuz.mm"
include "eleq2s.mm"
include "adantl.mm"
include "peano2nn.mm"
include "fvconst2g.mm"
include "sylan2.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "expnnval.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "exp1.mm"
include "mulid2.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "simpr.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "oveq2.mm"
include "exp0.mm"
include "sylan9eqr.mm"
include "jaodan.mm"
include "sylan2b.mm"

theorem expp1
  let cA: class A
  let cN: class N


  assert |- ( ( A e. CC /\ N e. NN0 ) -> ( A ^ ( N + 1 ) ) = ( ( A ^ N ) x. A ) )

  proof
    cN
    cn0
    wcel
    cA
    cc
    wcel
    #
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    cA
    cN
    c1
    caddc
    co
    #
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    cA
    cmul
    co
    #
    wceq
    #
    cN
    elnn0
    @0
    @1
    @7
    @2
    @0
    @1
    wa
    #
    @3
    cmul
    cn
    cA
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    cN
    @10
    cfv
    #
    cA
    cmul
    co
    #
    @4
    @6
    @8
    @11
    @12
    @3
    @9
    cfv
    #
    cmul
    co
    #
    @13
    @1
    @11
    @15
    wceq
    #
    @0
    @16
    cN
    c1
    cuz
    cfv
    cn
    cmul
    @9
    c1
    cN
    seqp1
    nnuz
    eleq2s
    adantl
    @8
    @14
    cA
    @12
    cmul
    @1
    @0
    @3
    cn
    wcel
    #
    @14
    cA
    wceq
    cN
    peano2nn
    #
    cn
    cA
    @3
    cc
    fvconst2g
    sylan2
    oveq2d
    eqtrd
    @1
    @0
    @17
    @4
    @11
    wceq
    @18
    cA
    @3
    expnnval
    sylan2
    @8
    @5
    @12
    cA
    cmul
    cA
    cN
    expnnval
    oveq1d
    3eqtr4d
    @0
    @2
    wa
    #
    cA
    c1
    cexp
    co
    #
    c1
    cA
    cmul
    co
    #
    @4
    @6
    @0
    @20
    @21
    wceq
    @2
    @0
    @20
    cA
    @21
    cA
    exp1
    cA
    mulid2
    eqtr4d
    adantr
    @19
    @3
    c1
    cA
    cexp
    @19
    @3
    cc0
    c1
    caddc
    co
    c1
    @19
    cN
    cc0
    c1
    caddc
    @0
    @2
    simpr
    oveq1d
    0p1e1
    syl6eq
    oveq2d
    @19
    @5
    c1
    cA
    cmul
    @2
    @0
    @5
    cA
    cc0
    cexp
    co
    c1
    cN
    cc0
    cA
    cexp
    oveq2
    cA
    exp0
    sylan9eqr
    oveq1d
    3eqtr4d
    jaodan
    sylan2b
end
