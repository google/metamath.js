include "wprt.mm"
include "cv.mm"
include "wcel.mm"
include "wel.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wex.mm"
include "df-rex.mm"
include "an32.mm"
include "weq.mm"
include "prtlem14.mm"
include "elequ2.mm"
include "biimprd.mm"
include "syl8.mm"
include "exp4a.mm"
include "impd.mm"
include "syl5bir.mm"
include "expd.mm"
include "imp5a.mm"
include "imp4b.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "ex.mm"

theorem prtlem17
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint w y
  assert |- ( Prt A -> ( ( x e. A /\ z e. x ) -> ( E. y e. A ( z e. y /\ w e. y ) -> w e. x ) ) )

  proof
    cA
    wprt
    #
    vx
    cv
    cA
    wcel
    #
    vz
    vx
    wel
    #
    wa
    #
    vz
    vy
    wel
    #
    vw
    vy
    wel
    #
    wa
    #
    vy
    cA
    wrex
    #
    vw
    vx
    wel
    #
    wi
    @7
    vy
    cv
    cA
    wcel
    #
    @6
    wa
    #
    vy
    wex
    @0
    @3
    wa
    #
    @8
    @6
    vy
    cA
    df-rex
    @11
    @10
    @8
    vy
    @0
    @3
    @9
    @6
    @8
    @0
    @3
    @9
    @4
    @5
    @8
    @0
    @3
    @9
    @4
    @5
    @8
    wi
    #
    wi
    #
    @3
    @9
    wa
    @1
    @9
    wa
    #
    @2
    wa
    @0
    @13
    @1
    @9
    @2
    an32
    @0
    @14
    @2
    @13
    @0
    @14
    @2
    @4
    @12
    @0
    @14
    @2
    @4
    wa
    vx
    vy
    weq
    #
    @12
    vx
    vy
    vz
    cA
    prtlem14
    @15
    @8
    @5
    vx
    vy
    vw
    elequ2
    biimprd
    syl8
    exp4a
    impd
    syl5bir
    expd
    imp5a
    imp4b
    exlimdv
    syl5bi
    ex
end
