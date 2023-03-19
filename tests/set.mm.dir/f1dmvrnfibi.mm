include "wcel.mm"
include "wf1.mm"
include "wa.mm"
include "cfn.mm"
include "crn.mm"
include "rnfi.mm"
include "cdm.mm"
include "cen.mm"
include "wbr.mm"
include "simpr.mm"
include "wf1o.mm"
include "wceq.mm"
include "wi.mm"
include "f1dm.mm"
include "f1f1orn.mm"
include "wb.mm"
include "eleq1.mm"
include "f1oeq2.mm"
include "anbi12d.mm"
include "eqcoms.mm"
include "biimpd.mm"
include "expcomd.mm"
include "sylc.mm"
include "impcom.mm"
include "adantr.mm"
include "f1oeng.mm"
include "syl.mm"
include "enfii.mm"
include "syl2anc.mm"
include "wfun.mm"
include "f1fun.mm"
include "ad2antlr.mm"
include "fundmfibi.mm"
include "mpbird.mm"
include "ex.mm"
include "impbid2.mm"

theorem f1dmvrnfibi
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V


  assert |- ( ( A e. V /\ F : A -1-1-> B ) -> ( F e. Fin <-> ran F e. Fin ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cB
    cF
    wf1
    #
    wa
    #
    cF
    cfn
    wcel
    #
    cF
    crn
    #
    cfn
    wcel
    #
    cF
    rnfi
    @2
    @5
    @3
    @2
    @5
    wa
    #
    @3
    cF
    cdm
    #
    cfn
    wcel
    #
    @6
    @5
    @7
    @4
    cen
    wbr
    #
    @8
    @2
    @5
    simpr
    @6
    @7
    cV
    wcel
    #
    @7
    @4
    cF
    wf1o
    #
    wa
    #
    @9
    @2
    @12
    @5
    @1
    @0
    @12
    @1
    @7
    cA
    wceq
    #
    cA
    @4
    cF
    wf1o
    #
    @0
    @12
    wi
    cA
    cB
    cF
    f1dm
    cA
    cB
    cF
    f1f1orn
    @13
    @0
    @14
    @12
    @13
    @0
    @14
    wa
    #
    @12
    @15
    @12
    wb
    cA
    @7
    cA
    @7
    wceq
    @0
    @10
    @14
    @11
    cA
    @7
    cV
    eleq1
    cA
    @7
    @4
    cF
    f1oeq2
    anbi12d
    eqcoms
    biimpd
    expcomd
    sylc
    impcom
    adantr
    @7
    @4
    cV
    cF
    f1oeng
    syl
    @7
    @4
    enfii
    syl2anc
    @6
    cF
    wfun
    #
    @3
    @8
    wb
    @1
    @16
    @0
    @5
    cA
    cB
    cF
    f1fun
    ad2antlr
    cF
    fundmfibi
    syl
    mpbird
    ex
    impbid2
end
