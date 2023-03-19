include "wdisj.mm"
include "cv.mm"
include "wcel.mm"
include "wrmo.mm"
include "wal.mm"
include "wa.mm"
include "wmo.mm"
include "df-disj.mm"
include "df-rmo.mm"
include "albii.mm"
include "bitri.mm"

theorem dfdisj2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( Disj_ x e. A B <-> A. y E* x ( x e. A /\ y e. B ) )

  proof
    vx
    cA
    cB
    wdisj
    vy
    cv
    cB
    wcel
    #
    vx
    cA
    wrmo
    #
    vy
    wal
    vx
    cv
    cA
    wcel
    @0
    wa
    vx
    wmo
    #
    vy
    wal
    vx
    vy
    cA
    cB
    df-disj
    @1
    @2
    vy
    @0
    vx
    cA
    df-rmo
    albii
    bitri
end
