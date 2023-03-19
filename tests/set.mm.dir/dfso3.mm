include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "w3a.mm"
include "wor.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "ne0i.mm"
include "r19.27zv.mm"
include "syl.mm"
include "ralbiia.mm"
include "ralbii.mm"
include "df-3an.mm"
include "2ralbii.mm"
include "wpo.mm"
include "df-po.mm"
include "anbi1i.mm"
include "df-so.mm"
include "r19.26-2.mm"
include "3bitr4i.mm"
include "3bitr4ri.mm"

theorem dfso3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint R z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  assert |- ( R Or A <-> A. x e. A A. y e. A A. z e. A ( -. x R x /\ ( ( x R y /\ y R z ) -> x R z ) /\ ( x R y \/ x = y \/ y R x ) ) )

  proof
    vx
    cv
    #
    @0
    cR
    wbr
    wn
    #
    @0
    vy
    cv
    #
    cR
    wbr
    #
    @2
    vz
    cv
    #
    cR
    wbr
    wa
    @0
    @4
    cR
    wbr
    wi
    #
    wa
    #
    @3
    vx
    vy
    weq
    @2
    @0
    cR
    wbr
    w3o
    #
    wa
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    @6
    vz
    cA
    wral
    #
    @7
    wa
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    @1
    @5
    @7
    w3a
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    vx
    cA
    wral
    cA
    cR
    wor
    #
    @10
    @13
    vx
    cA
    @9
    @12
    vy
    cA
    @2
    cA
    wcel
    cA
    c0
    wne
    @9
    @12
    wb
    cA
    @2
    ne0i
    @6
    @7
    vz
    cA
    r19.27zv
    syl
    ralbiia
    ralbii
    @16
    @9
    vx
    vy
    cA
    cA
    @15
    @8
    vz
    cA
    @1
    @5
    @7
    df-3an
    ralbii
    2ralbii
    cA
    cR
    wpo
    #
    @7
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    @11
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @19
    wa
    @17
    @14
    @18
    @20
    @19
    vx
    vy
    vz
    cA
    cR
    df-po
    anbi1i
    vx
    vy
    cA
    cR
    df-so
    @11
    @7
    vx
    vy
    cA
    cA
    r19.26-2
    3bitr4i
    3bitr4ri
end
