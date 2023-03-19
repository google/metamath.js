include "cv.mm"
include "wss.mm"
include "cdm.mm"
include "wfn.mm"
include "wa.mm"
include "wex.mm"
include "df-ac.mm"
include "axaci.mm"

theorem ac7
  let vx: setvar x
  let vf: setvar f

  disjoint f x
  assert |- E. f ( f C_ x /\ f Fn dom x )

  proof
    vf
    cv
    #
    vx
    cv
    #
    wss
    @0
    @1
    cdm
    wfn
    wa
    vf
    wex
    vx
    vx
    vf
    df-ac
    axaci
end
