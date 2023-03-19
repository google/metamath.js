include "wf1.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "f1f.mm"
include "fss.mm"
include "sylan.mm"
include "df-f1.mm"
include "simprbi.mm"
include "adantr.mm"
include "sylanbrc.mm"

theorem f1ss
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A -1-1-> B /\ B C_ C ) -> F : A -1-1-> C )

  proof
    cA
    cB
    cF
    wf1
    #
    cB
    cC
    wss
    #
    wa
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
    @0
    cA
    cB
    cF
    wf
    #
    @1
    @2
    cA
    cB
    cF
    f1f
    cA
    cB
    cC
    cF
    fss
    sylan
    @0
    @3
    @1
    @0
    @4
    @3
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
