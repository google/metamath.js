include "wf1.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "wfn.mm"
include "f1fn.mm"
include "adantr.mm"
include "simpr.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "df-f1.mm"
include "simprbi.mm"

theorem f1ssr
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A -1-1-> B /\ ran F C_ C ) -> F : A -1-1-> C )

  proof
    cA
    cB
    cF
    wf1
    #
    cF
    crn
    cC
    wss
    #
    wa
    #
    cA
    cC
    cF
    wf
    #
    cF
    ccnv
    wfun
    #
    cA
    cC
    cF
    wf1
    @2
    cF
    cA
    wfn
    #
    @1
    @3
    @0
    @5
    @1
    cA
    cB
    cF
    f1fn
    adantr
    @0
    @1
    simpr
    cA
    cC
    cF
    df-f
    sylanbrc
    @0
    @4
    @1
    @0
    cA
    cB
    cF
    wf
    @4
    cA
    cB
    cF
    df-f1
    simprbi
    adantr
    cA
    cC
    cF
    df-f1
    sylanbrc
end
