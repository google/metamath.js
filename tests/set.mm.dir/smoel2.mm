include "wfn.mm"
include "wsmo.mm"
include "wa.mm"
include "wcel.mm"
include "cfv.mm"
include "cdm.mm"
include "fndm.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "biimprd.mm"
include "smoel.mm"
include "3expib.mm"
include "sylan9.mm"
include "imp.mm"

theorem smoel2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( ( F Fn A /\ Smo F ) /\ ( B e. A /\ C e. B ) ) -> ( F ` C ) e. ( F ` B ) )

  proof
    cF
    cA
    wfn
    #
    cF
    wsmo
    #
    wa
    cB
    cA
    wcel
    #
    cC
    cB
    wcel
    #
    wa
    #
    cC
    cF
    cfv
    cB
    cF
    cfv
    wcel
    #
    @0
    @4
    cB
    cF
    cdm
    #
    wcel
    #
    @3
    wa
    #
    @1
    @5
    @0
    @8
    @4
    @0
    @7
    @2
    @3
    @0
    @6
    cA
    cB
    cA
    cF
    fndm
    eleq2d
    anbi1d
    biimprd
    @1
    @7
    @3
    @5
    cB
    cF
    cC
    smoel
    3expib
    sylan9
    imp
end
