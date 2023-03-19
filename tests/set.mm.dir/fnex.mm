include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "wrel.mm"
include "cdm.mm"
include "cres.mm"
include "cvv.mm"
include "fnrel.mm"
include "adantr.mm"
include "wfun.mm"
include "wceq.mm"
include "df-fn.mm"
include "eleq1a.mm"
include "impcom.mm"
include "resfunexg.mm"
include "sylan2.mm"
include "anassrs.mm"
include "sylanb.mm"
include "resdm.mm"
include "eleq1d.mm"
include "biimpa.mm"
include "syl2anc.mm"

theorem fnex
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F Fn A /\ A e. B ) -> F e. _V )

  proof
    cF
    cA
    wfn
    #
    cA
    cB
    wcel
    #
    wa
    cF
    wrel
    #
    cF
    cF
    cdm
    #
    cres
    #
    cvv
    wcel
    #
    cF
    cvv
    wcel
    #
    @0
    @2
    @1
    cA
    cF
    fnrel
    adantr
    @0
    cF
    wfun
    #
    @3
    cA
    wceq
    #
    wa
    @1
    @5
    cF
    cA
    df-fn
    @7
    @8
    @1
    @5
    @8
    @1
    wa
    @7
    @3
    cB
    wcel
    #
    @5
    @1
    @8
    @9
    cA
    cB
    @3
    eleq1a
    impcom
    cF
    @3
    cB
    resfunexg
    sylan2
    anassrs
    sylanb
    @2
    @5
    @6
    @2
    @4
    cF
    cvv
    cF
    resdm
    eleq1d
    biimpa
    syl2anc
end
