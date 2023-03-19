include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "pjfni.mm"
include "pjrni.mm"
include "chssii.mm"
include "eqsstri.mm"
include "df-f.mm"
include "mpbir2an.mm"

theorem pjfi
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pjfn.1: |- H e. CH


  assert |- ( projh ` H ) : ~H --> ~H

  proof
    chil
    chil
    cH
    cpjh
    cfv
    #
    wf
    @0
    chil
    wfn
    @0
    crn
    #
    chil
    wss
    cH
    pjfn.1
    pjfni
    @1
    cH
    chil
    cH
    pjfn.1
    pjrni
    cH
    pjfn.1
    chssii
    eqsstri
    chil
    chil
    @0
    df-f
    mpbir2an
end
