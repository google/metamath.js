include "cps.mm"
include "wcel.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "cuni.mm"
include "pslem.mm"
include "simp3d.mm"
include "3impib.mm"

theorem psasym
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( ( R e. PosetRel /\ A R B /\ B R A ) -> A = B )

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
    cA
    cR
    wbr
    #
    cA
    cB
    wceq
    #
    @0
    @1
    @2
    wa
    #
    cA
    cA
    cR
    wbr
    #
    wi
    cA
    cR
    cuni
    cuni
    wcel
    @5
    wi
    @4
    @3
    wi
    cA
    cB
    cA
    cR
    pslem
    simp3d
    3impib
end
