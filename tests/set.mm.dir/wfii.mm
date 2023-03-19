include "wwe.mm"
include "wse.mm"
include "wss.mm"
include "cv.mm"
include "cpred.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "wfi.mm"
include "mpanl12.mm"

theorem wfii
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  assume wfi.1: |- R We A
  assume wfi.2: |- R Se A

  disjoint A y
  disjoint B y
  disjoint R y
  assert |- ( ( B C_ A /\ A. y e. A ( Pred ( R , A , y ) C_ B -> y e. B ) ) -> A = B )

  proof
    cA
    cR
    wwe
    cA
    cR
    wse
    cB
    cA
    wss
    cA
    cR
    vy
    cv
    #
    cpred
    cB
    wss
    @0
    cB
    wcel
    wi
    vy
    cA
    wral
    wa
    cA
    cB
    wceq
    wfi.1
    wfi.2
    vy
    cA
    cB
    cR
    wfi
    mpanl12
end
