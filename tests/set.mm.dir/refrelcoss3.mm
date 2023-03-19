include "cv.mm"
include "wceq.mm"
include "ccoss.mm"
include "wbr.mm"
include "wi.mm"
include "crn.mm"
include "wral.mm"
include "cdm.mm"
include "wrel.mm"
include "refrelcosslem.mm"
include "idinxpssinxp4.mm"
include "mpbir.mm"
include "rncossdmcoss.mm"
include "raleqi.mm"
include "ralbii.mm"
include "relcoss.mm"
include "pm3.2i.mm"

theorem refrelcoss3
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- ( A. x e. dom ,~ R A. y e. ran ,~ R ( x = y -> x ,~ R y ) /\ Rel ,~ R )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wceq
    @0
    @1
    cR
    ccoss
    #
    wbr
    wi
    #
    vy
    @2
    crn
    #
    wral
    #
    vx
    @2
    cdm
    #
    wral
    #
    @2
    wrel
    @7
    @3
    vy
    @6
    wral
    #
    vx
    @6
    wral
    #
    @9
    @0
    @0
    @2
    wbr
    vx
    @6
    wral
    vx
    cR
    refrelcosslem
    vx
    vy
    @6
    @2
    idinxpssinxp4
    mpbir
    @5
    @8
    vx
    @6
    @3
    vy
    @4
    @6
    cR
    rncossdmcoss
    raleqi
    ralbii
    mpbir
    cR
    relcoss
    pm3.2i
end
