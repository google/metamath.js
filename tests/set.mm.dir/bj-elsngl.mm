include "bj-csngl.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "csn.mm"
include "wrex.mm"
include "df-clel.mm"
include "df-bj-sngl.mm"
include "abeq2i.mm"
include "anbi2i.mm"
include "exbii.mm"
include "r19.42v.mm"
include "bicomi.mm"
include "rexcom4.mm"
include "eqcom.mm"
include "snex.mm"
include "eqvinc.mm"
include "exancom.mm"
include "3bitri.mm"
include "rexbii.mm"

theorem bj-elsngl
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A e. sngl B <-> E. x e. B A = { x } )

  proof
    cA
    cB
    bj-csngl
    #
    wcel
    vy
    cv
    #
    cA
    wceq
    #
    @1
    @0
    wcel
    #
    wa
    #
    vy
    wex
    @2
    @1
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    cB
    wrex
    #
    wa
    #
    vy
    wex
    #
    cA
    @6
    wceq
    #
    vx
    cB
    wrex
    #
    vy
    cA
    @0
    df-clel
    @4
    @9
    vy
    @3
    @8
    @2
    @8
    vy
    @0
    vy
    vx
    cB
    df-bj-sngl
    abeq2i
    anbi2i
    exbii
    @10
    @2
    @7
    wa
    #
    vx
    cB
    wrex
    #
    vy
    wex
    #
    @13
    vy
    wex
    #
    vx
    cB
    wrex
    #
    @12
    @9
    @14
    vy
    @14
    @9
    @2
    @7
    vx
    cB
    r19.42v
    bicomi
    exbii
    @17
    @15
    @13
    vx
    vy
    cB
    rexcom4
    bicomi
    @16
    @11
    vx
    cB
    @11
    @16
    @11
    @6
    cA
    wceq
    @7
    @2
    wa
    vy
    wex
    @16
    cA
    @6
    eqcom
    vy
    @6
    cA
    @5
    snex
    eqvinc
    @7
    @2
    vy
    exancom
    3bitri
    bicomi
    rexbii
    3bitri
    3bitri
end
