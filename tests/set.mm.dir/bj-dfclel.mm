include "wel.mm"
include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "cleljust.mm"
include "gen2.mm"
include "bj-df-clel.mm"

theorem bj-dfclel
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w

  disjoint A x
  disjoint B x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint A v
  disjoint w x
  disjoint A w
  disjoint B u
  disjoint B v
  disjoint B w
  assert |- ( A e. B <-> E. x ( x = A /\ x e. B ) )

  proof
    vx
    vw
    vv
    vu
    cA
    cB
    vu
    vv
    wel
    vw
    vu
    weq
    vw
    vv
    wel
    wa
    vw
    wex
    wb
    vu
    vv
    vu
    vv
    vw
    cleljust
    gen2
    bj-df-clel
end
