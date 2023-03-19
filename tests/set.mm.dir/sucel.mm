include "csuc.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wo.mm"
include "wb.mm"
include "wal.mm"
include "risset.mm"
include "dfcleq.mm"
include "vex.mm"
include "elsuc.mm"
include "bibi2i.mm"
include "albii.mm"
include "bitri.mm"
include "rexbii.mm"

theorem sucel
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  assert |- ( suc A e. B <-> E. x e. B A. y ( y e. x <-> ( y e. A \/ y = A ) ) )

  proof
    cA
    csuc
    #
    cB
    wcel
    vx
    cv
    #
    @0
    wceq
    #
    vx
    cB
    wrex
    vy
    cv
    #
    @1
    wcel
    #
    @3
    cA
    wcel
    @3
    cA
    wceq
    wo
    #
    wb
    #
    vy
    wal
    #
    vx
    cB
    wrex
    vx
    @0
    cB
    risset
    @2
    @7
    vx
    cB
    @2
    @4
    @3
    @0
    wcel
    #
    wb
    #
    vy
    wal
    @7
    vy
    @1
    @0
    dfcleq
    @9
    @6
    vy
    @8
    @5
    @4
    @3
    cA
    vy
    vex
    elsuc
    bibi2i
    albii
    bitri
    rexbii
    bitri
end
