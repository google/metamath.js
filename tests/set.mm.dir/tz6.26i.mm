include "wwe.mm"
include "wse.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cpred.mm"
include "wceq.mm"
include "wrex.mm"
include "tz6.26.mm"
include "mpanl12.mm"

theorem tz6.26i
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  assume tz6.26i.1: |- R We A
  assume tz6.26i.2: |- R Se A

  disjoint A y
  disjoint B y
  disjoint R y
  assert |- ( ( B C_ A /\ B =/= (/) ) -> E. y e. B Pred ( R , B , y ) = (/) )

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
    cB
    c0
    wne
    wa
    cB
    cR
    vy
    cv
    cpred
    c0
    wceq
    vy
    cB
    wrex
    tz6.26i.1
    tz6.26i.2
    vy
    cA
    cB
    cR
    tz6.26
    mpanl12
end
