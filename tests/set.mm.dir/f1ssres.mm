include "wf1.mm"
include "wss.mm"
include "wa.mm"
include "cres.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "f1f.mm"
include "fssres.mm"
include "sylan.mm"
include "df-f1.mm"
include "simprbi.mm"
include "funres11.mm"
include "syl.mm"
include "adantr.mm"
include "sylanbrc.mm"

theorem f1ssres
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A -1-1-> B /\ C C_ A ) -> ( F |` C ) : C -1-1-> B )

  proof
    cA
    cB
    cF
    wf1
    #
    cC
    cA
    wss
    #
    wa
    cC
    cB
    cF
    cC
    cres
    #
    wf
    #
    @2
    ccnv
    wfun
    #
    cC
    cB
    @2
    wf1
    @0
    cA
    cB
    cF
    wf
    #
    @1
    @3
    cA
    cB
    cF
    f1f
    cA
    cB
    cC
    cF
    fssres
    sylan
    @0
    @4
    @1
    @0
    cF
    ccnv
    wfun
    #
    @4
    @0
    @5
    @6
    cA
    cB
    cF
    df-f1
    simprbi
    cC
    cF
    funres11
    syl
    adantr
    cC
    cB
    @2
    df-f1
    sylanbrc
end
