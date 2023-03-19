include "cv.mm"
include "cop.mm"
include "copab.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "elopab.mm"
include "vex.mm"
include "opth.mm"
include "eqcom.mm"
include "bitr3i.mm"
include "anbi1i.mm"
include "2exbii.mm"
include "bitr4i.mm"

theorem opelopab4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u

  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( <. u , v >. e. { <. x , y >. | ph } <-> E. x E. y ( ( x = u /\ y = v ) /\ ph ) )

  proof
    vu
    cv
    #
    vv
    cv
    #
    cop
    #
    wph
    vx
    vy
    copab
    wcel
    @2
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    wph
    wa
    #
    vy
    wex
    vx
    wex
    @3
    @0
    wceq
    @4
    @1
    wceq
    wa
    #
    wph
    wa
    #
    vy
    wex
    vx
    wex
    wph
    vx
    vy
    @2
    elopab
    @9
    @7
    vx
    vy
    @8
    @6
    wph
    @8
    @5
    @2
    wceq
    @6
    @3
    @4
    @0
    @1
    vx
    vex
    vy
    vex
    opth
    @5
    @2
    eqcom
    bitr3i
    anbi1i
    2exbii
    bitr4i
end
