include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "wfun.mm"
include "fnex.mm"
include "fnfun.mm"
include "adantr.mm"
include "fundmeng.mm"
include "syl2anc.mm"
include "wb.mm"
include "fndm.mm"
include "breq1d.mm"
include "mpbid.mm"

theorem fndmeng
  let cA: class A
  let cC: class C
  let cF: class F


  assert |- ( ( F Fn A /\ A e. C ) -> A ~~ F )

  proof
    cF
    cA
    wfn
    #
    cA
    cC
    wcel
    #
    wa
    #
    cF
    cdm
    #
    cF
    cen
    wbr
    #
    cA
    cF
    cen
    wbr
    #
    @2
    cF
    cvv
    wcel
    cF
    wfun
    #
    @4
    cA
    cC
    cF
    fnex
    @0
    @6
    @1
    cA
    cF
    fnfun
    adantr
    cF
    cvv
    fundmeng
    syl2anc
    @0
    @4
    @5
    wb
    @1
    @0
    @3
    cA
    cF
    cen
    cA
    cF
    fndm
    breq1d
    adantr
    mpbid
end
