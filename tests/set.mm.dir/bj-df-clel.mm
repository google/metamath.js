include "df-clel.mm"

theorem bj-df-clel
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  assume bj-df-clel.1: |- A. u A. v ( u e. v <-> E. w ( w = u /\ w e. v ) )

  disjoint u v
  disjoint u w
  disjoint u x
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint A v
  disjoint w x
  disjoint A w
  disjoint A x
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  assert |- ( A e. B <-> E. x ( x = A /\ x e. B ) )

  proof
    vx
    cA
    cB
    df-clel
end
