include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wi.mm"
include "cab.mm"
include "wcel.mm"
include "wa.mm"
include "id.mm"
include "bj-vexwv.mm"
include "biantru.mm"
include "exbii.mm"
include "df-clel.mm"
include "3bitr2i.mm"
include "bicomi.mm"
include "bitri.mm"

theorem bj-denotes
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  assert |- ( E. x x = A <-> E. y y = A )

  proof
    vx
    cv
    #
    cA
    wceq
    #
    vx
    wex
    #
    vy
    cv
    #
    cA
    wceq
    #
    @3
    vz
    cv
    #
    @5
    wceq
    #
    @6
    wi
    #
    vz
    cab
    #
    wcel
    #
    wa
    #
    vy
    wex
    #
    @4
    vy
    wex
    @2
    @1
    @0
    @8
    wcel
    #
    wa
    #
    vx
    wex
    cA
    @8
    wcel
    @11
    @1
    @13
    vx
    @12
    @1
    @7
    vz
    vx
    @6
    id
    #
    bj-vexwv
    biantru
    exbii
    vx
    cA
    @8
    df-clel
    vy
    cA
    @8
    df-clel
    3bitr2i
    @10
    @4
    vy
    @4
    @10
    @9
    @4
    @7
    vz
    vy
    @14
    bj-vexwv
    biantru
    bicomi
    exbii
    bitri
end
