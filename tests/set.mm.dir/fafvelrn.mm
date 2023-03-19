include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cafv.mm"
include "crn.mm"
include "wfn.mm"
include "ffn.mm"
include "fnafvelrn.mm"
include "sylan.mm"
include "wi.mm"
include "frn.mm"
include "sseld.mm"
include "adantr.mm"
include "mpd.mm"

theorem fafvelrn
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F : A --> B /\ C e. A ) -> ( F ''' C ) e. B )

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
    cafv
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
    fnafvelrn
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
