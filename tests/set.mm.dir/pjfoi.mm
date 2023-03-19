include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "wfo.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "pjfni.mm"
include "pjrni.mm"
include "df-fo.mm"
include "mpbir2an.mm"

theorem pjfoi
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pjfn.1: |- H e. CH


  assert |- ( projh ` H ) : ~H -onto-> H

  proof
    chil
    cH
    cH
    cpjh
    cfv
    #
    wfo
    @0
    chil
    wfn
    @0
    crn
    cH
    wceq
    cH
    pjfn.1
    pjfni
    cH
    pjfn.1
    pjrni
    chil
    cH
    @0
    df-fo
    mpbir2an
end
