include "wceq.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "funsneqop.mm"
include "funsndifnop.mm"
include "necon4ai.mm"
include "impbii.mm"

theorem funsneqopb
  let cA: class A
  let cB: class B
  let cG: class G
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  assume funsndifnop.a: |- A e. _V
  assume funsndifnop.b: |- B e. _V
  assume funsndifnop.g: |- G = { <. A , B >. }


  assert |- ( A = B <-> G e. ( _V X. _V ) )

  proof
    cA
    cB
    wceq
    cG
    cvv
    cvv
    cxp
    wcel
    #
    cA
    cB
    cG
    funsndifnop.a
    funsndifnop.b
    funsndifnop.g
    funsneqop
    @0
    cA
    cB
    cA
    cB
    cG
    funsndifnop.a
    funsndifnop.b
    funsndifnop.g
    funsndifnop
    necon4ai
    impbii
end
