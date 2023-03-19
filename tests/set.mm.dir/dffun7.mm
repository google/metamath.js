include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "wa.mm"
include "cdm.mm"
include "wral.mm"
include "dffun6.mm"
include "wcel.mm"
include "wi.mm"
include "wex.mm"
include "moabs.mm"
include "vex.mm"
include "eldm.mm"
include "imbi1i.mm"
include "bitr4i.mm"
include "albii.mm"
include "df-ral.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem dffun7
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( Fun A <-> ( Rel A /\ A. x e. dom A E* y x A y ) )

  proof
    cA
    wfun
    cA
    wrel
    #
    vx
    cv
    #
    vy
    cv
    cA
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    #
    wa
    @0
    @3
    vx
    cA
    cdm
    #
    wral
    #
    wa
    vx
    vy
    cA
    dffun6
    @4
    @6
    @0
    @4
    @1
    @5
    wcel
    #
    @3
    wi
    #
    vx
    wal
    @6
    @3
    @8
    vx
    @3
    @2
    vy
    wex
    #
    @3
    wi
    @8
    @2
    vy
    moabs
    @7
    @9
    @3
    vy
    @1
    cA
    vx
    vex
    eldm
    imbi1i
    bitr4i
    albii
    @3
    vx
    @5
    df-ral
    bitr4i
    anbi2i
    bitri
end
