include "cab.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "wal.mm"
include "df-clel.mm"
include "abeq2.mm"
include "anbi2ci.mm"
include "exbii.mm"
include "bitri.mm"

theorem clabel
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A y
  disjoint ph y
  disjoint x y
  assert |- ( { x | ph } e. A <-> E. y ( y e. A /\ A. x ( x e. y <-> ph ) ) )

  proof
    wph
    vx
    cab
    #
    cA
    wcel
    vy
    cv
    #
    @0
    wceq
    #
    @1
    cA
    wcel
    #
    wa
    #
    vy
    wex
    @3
    vx
    cv
    @1
    wcel
    wph
    wb
    vx
    wal
    #
    wa
    #
    vy
    wex
    vy
    @0
    cA
    df-clel
    @4
    @6
    vy
    @2
    @5
    @3
    wph
    vx
    @1
    abeq2
    anbi2ci
    exbii
    bitri
end
