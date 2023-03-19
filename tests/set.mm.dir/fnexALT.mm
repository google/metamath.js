include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "wss.mm"
include "cvv.mm"
include "wrel.mm"
include "fnrel.mm"
include "relssdmrn.mm"
include "syl.mm"
include "adantr.mm"
include "fndm.mm"
include "eleq1d.mm"
include "biimpar.mm"
include "cima.mm"
include "wfun.mm"
include "fnfun.mm"
include "funimaexg.mm"
include "sylan.mm"
include "imadmrn.mm"
include "imaeq2d.mm"
include "syl5eqr.mm"
include "syldan.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "ssexg.mm"

theorem fnexALT
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
    #
    cF
    cF
    cdm
    #
    cF
    crn
    #
    cxp
    #
    wss
    #
    @5
    cvv
    wcel
    #
    cF
    cvv
    wcel
    @0
    @6
    @1
    @0
    cF
    wrel
    @6
    cA
    cF
    fnrel
    cF
    relssdmrn
    syl
    adantr
    @2
    @3
    cB
    wcel
    #
    @4
    cvv
    wcel
    #
    @7
    @0
    @8
    @1
    @0
    @3
    cA
    cB
    cA
    cF
    fndm
    #
    eleq1d
    biimpar
    @0
    @1
    cF
    cA
    cima
    #
    cvv
    wcel
    #
    @9
    @0
    cF
    wfun
    @1
    @12
    cA
    cF
    fnfun
    cF
    cA
    cB
    funimaexg
    sylan
    @0
    @9
    @12
    @0
    @4
    @11
    cvv
    @0
    @4
    cF
    @3
    cima
    @11
    cF
    imadmrn
    @0
    @3
    cA
    cF
    @10
    imaeq2d
    syl5eqr
    eleq1d
    biimpar
    syldan
    @3
    @4
    cB
    cvv
    xpexg
    syl2anc
    cF
    @5
    cvv
    ssexg
    syl2anc
end
