include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "crn.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "wi.mm"
include "frn.mm"
include "sseld.mm"
include "adantr.mm"
include "mpd.mm"

theorem ffvelrn
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A --> B /\ C e. A ) -> ( F ` C ) e. B )

  proof
    cA
    cB
    cF
    wf
    #
    cC
    cA
    wcel
    #
    wa
    cC
    cF
    cfv
    #
    cF
    crn
    #
    wcel
    #
    @2
    cB
    wcel
    #
    @0
    cF
    cA
    wfn
    @1
    @4
    cA
    cB
    cF
    ffn
    cA
    cC
    cF
    fnfvelrn
    sylan
    @0
    @4
    @5
    wi
    @1
    @0
    @3
    cB
    @2
    cA
    cB
    cF
    frn
    sseld
    adantr
    mpd
end
