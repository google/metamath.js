include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "ciun.mm"
include "wal.mm"
include "wb.mm"
include "wa.mm"
include "wex.mm"
include "eleq2.mm"
include "anbi1d.mm"
include "alexbii.mm"
include "df-rex.mm"
include "3bitr4g.mm"
include "syl.mm"
include "abbidv.mm"
include "df-iun.mm"
include "3eqtr4g.mm"

theorem bnj956
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume bnj956.1: |- ( A = B -> A. x A = B )


  assert |- ( A = B -> U_ x e. A C = U_ x e. B C )

  proof
    cA
    cB
    wceq
    #
    vy
    cv
    cC
    wcel
    #
    vx
    cA
    wrex
    #
    vy
    cab
    @1
    vx
    cB
    wrex
    #
    vy
    cab
    vx
    cA
    cC
    ciun
    vx
    cB
    cC
    ciun
    @0
    @2
    @3
    vy
    @0
    @0
    vx
    wal
    #
    @2
    @3
    wb
    bnj956.1
    @4
    vx
    cv
    #
    cA
    wcel
    #
    @1
    wa
    #
    vx
    wex
    @5
    cB
    wcel
    #
    @1
    wa
    #
    vx
    wex
    @2
    @3
    @0
    @7
    @9
    vx
    @0
    @6
    @8
    @1
    cA
    cB
    @5
    eleq2
    anbi1d
    alexbii
    @1
    vx
    cA
    df-rex
    @1
    vx
    cB
    df-rex
    3bitr4g
    syl
    abbidv
    vx
    vy
    cA
    cC
    df-iun
    vx
    vy
    cB
    cC
    df-iun
    3eqtr4g
end
