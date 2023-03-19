include "cps.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "cuni.mm"
include "wceq.mm"
include "pslem.mm"
include "simp1d.mm"
include "3impib.mm"

theorem pstr
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( ( R e. PosetRel /\ A R B /\ B R C ) -> A R C )

  proof
    cR
    cps
    wcel
    #
    cA
    cB
    cR
    wbr
    #
    cB
    cC
    cR
    wbr
    #
    cA
    cC
    cR
    wbr
    #
    @0
    @1
    @2
    wa
    @3
    wi
    cA
    cR
    cuni
    cuni
    wcel
    cA
    cA
    cR
    wbr
    wi
    @1
    cB
    cA
    cR
    wbr
    wa
    cA
    cB
    wceq
    wi
    cA
    cB
    cC
    cR
    pslem
    simp1d
    3impib
end
