include "wfr.mm"
include "wse.mm"
include "wss.mm"
include "cv.mm"
include "cpred.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "frind.mm"
include "mpanl12.mm"

theorem frindi
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  assume frind.1: |- R Fr A
  assume frind.2: |- R Se A

  disjoint A y
  disjoint B y
  disjoint R y
  assert |- ( ( B C_ A /\ A. y e. A ( Pred ( R , A , y ) C_ B -> y e. B ) ) -> A = B )

  proof
    cA
    cR
    wfr
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
    frind.1
    frind.2
    vy
    cA
    cB
    cR
    frind
    mpanl12
end
