include "c0.mm"
include "cv.mm"
include "wcel.mm"
include "csuc.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "wel.mm"
include "wn.mm"
include "wal.mm"
include "weq.mm"
include "wo.mm"
include "wb.mm"
include "wi.mm"
include "ax-inf2.mm"
include "wrex.mm"
include "0el.mm"
include "df-rex.mm"
include "bitri.mm"
include "sucel.mm"
include "ralbii.mm"
include "df-ral.mm"
include "anbi12i.mm"
include "exbii.mm"
include "mpbir.mm"

theorem zfinf2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  assert |- E. x ( (/) e. x /\ A. y e. x suc y e. x )

  proof
    c0
    vx
    cv
    #
    wcel
    #
    vy
    cv
    #
    csuc
    @0
    wcel
    #
    vy
    @0
    wral
    #
    wa
    #
    vx
    wex
    vy
    vx
    wel
    #
    vz
    vy
    wel
    wn
    vz
    wal
    #
    wa
    vy
    wex
    #
    @6
    vz
    vx
    wel
    vw
    vz
    wel
    vw
    vy
    wel
    vw
    vy
    weq
    wo
    wb
    vw
    wal
    #
    wa
    vz
    wex
    #
    wi
    vy
    wal
    #
    wa
    #
    vx
    wex
    vx
    vy
    vz
    vw
    ax-inf2
    @5
    @12
    vx
    @1
    @8
    @4
    @11
    @1
    @7
    vy
    @0
    wrex
    @8
    vy
    vz
    @0
    0el
    @7
    vy
    @0
    df-rex
    bitri
    @4
    @10
    vy
    @0
    wral
    @11
    @3
    @10
    vy
    @0
    @3
    @9
    vz
    @0
    wrex
    @10
    vz
    vw
    @2
    @0
    sucel
    @9
    vz
    @0
    df-rex
    bitri
    ralbii
    @10
    vy
    @0
    df-ral
    bitri
    anbi12i
    exbii
    mpbir
end
