include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "dfac3.mm"
include "axaci.mm"

theorem ac4
  let vx: setvar x
  let vz: setvar z
  let vf: setvar f

  disjoint x z
  disjoint f x
  disjoint f z
  assert |- E. f A. z e. x ( z =/= (/) -> ( f ` z ) e. z )

  proof
    vz
    cv
    #
    c0
    wne
    @0
    vf
    cv
    cfv
    @0
    wcel
    wi
    vz
    vx
    cv
    wral
    vf
    wex
    vx
    vx
    vz
    vf
    dfac3
    axaci
end
