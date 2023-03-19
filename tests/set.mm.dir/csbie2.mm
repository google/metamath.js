include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "csb.mm"
include "gen2.mm"
include "csbie2t.mm"
include "ax-mp.mm"

theorem csbie2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume csbie2t.1: |- A e. _V
  assume csbie2t.2: |- B e. _V
  assume csbie2.3: |- ( ( x = A /\ y = B ) -> C = D )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint D x
  disjoint D y
  assert |- [_ A / x ]_ [_ B / y ]_ C = D

  proof
    vx
    cv
    cA
    wceq
    vy
    cv
    cB
    wceq
    wa
    cC
    cD
    wceq
    wi
    #
    vy
    wal
    vx
    wal
    vx
    cA
    vy
    cB
    cC
    csb
    csb
    cD
    wceq
    @0
    vx
    vy
    csbie2.3
    gen2
    vx
    vy
    cA
    cB
    cC
    cD
    csbie2t.1
    csbie2t.2
    csbie2t
    ax-mp
end
