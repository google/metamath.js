include "wfun.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "fununiq.mm"
include "expdimp.mm"
include "wi.mm"
include "breq2.mm"
include "biimpcd.mm"
include "adantl.mm"
include "impbid.mm"

theorem funbreq
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume funbreq.1: |- A e. _V
  assume funbreq.2: |- B e. _V
  assume funbreq.3: |- C e. _V


  assert |- ( ( Fun F /\ A F B ) -> ( A F C <-> B = C ) )

  proof
    cF
    wfun
    #
    cA
    cB
    cF
    wbr
    #
    wa
    cA
    cC
    cF
    wbr
    #
    cB
    cC
    wceq
    #
    @0
    @1
    @2
    @3
    cA
    cB
    cC
    cF
    funbreq.1
    funbreq.2
    funbreq.3
    fununiq
    expdimp
    @1
    @3
    @2
    wi
    @0
    @3
    @1
    @2
    cB
    cC
    cA
    cF
    breq2
    biimpcd
    adantl
    impbid
end
