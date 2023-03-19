include "cc.mm"
include "wcel.mm"
include "cshi.mm"
include "co.mm"
include "cdm.mm"
include "cv.mm"
include "cmin.mm"
include "wbr.mm"
include "wa.mm"
include "copab.mm"
include "crab.mm"
include "shftfval.mm"
include "dmeqd.mm"
include "wex.mm"
include "cab.mm"
include "19.42v.mm"
include "ovex.mm"
include "eldm.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "abbii.mm"
include "dmopab.mm"
include "df-rab.mm"
include "3eqtr4i.mm"
include "syl6eq.mm"

theorem shftdm
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  assume shftfval.1: |- F e. _V

  disjoint A x
  disjoint F x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( A e. CC -> dom ( F shift A ) = { x e. CC | ( x - A ) e. dom F } )

  proof
    cA
    cc
    wcel
    #
    cF
    cA
    cshi
    co
    #
    cdm
    vx
    cv
    #
    cc
    wcel
    #
    @2
    cA
    cmin
    co
    #
    vy
    cv
    cF
    wbr
    #
    wa
    #
    vx
    vy
    copab
    #
    cdm
    #
    @4
    cF
    cdm
    wcel
    #
    vx
    cc
    crab
    #
    @0
    @1
    @7
    vx
    vy
    cA
    cF
    shftfval.1
    shftfval
    dmeqd
    @6
    vy
    wex
    #
    vx
    cab
    @3
    @9
    wa
    #
    vx
    cab
    @8
    @10
    @11
    @12
    vx
    @11
    @3
    @5
    vy
    wex
    #
    wa
    @12
    @3
    @5
    vy
    19.42v
    @9
    @13
    @3
    vy
    @4
    cF
    @2
    cA
    cmin
    ovex
    eldm
    anbi2i
    bitr4i
    abbii
    @6
    vx
    vy
    dmopab
    @9
    vx
    cc
    df-rab
    3eqtr4i
    syl6eq
end
