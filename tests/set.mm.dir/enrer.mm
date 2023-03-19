include "cpp.mm"
include "cer.mm"
include "cnp.mm"
include "df-enr.mm"
include "cv.mm"
include "addcompr.mm"
include "addclpr.mm"
include "addasspr.mm"
include "addcanpr.mm"
include "ecopover.mm"

theorem enrer
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u


  assert |- ~R Er ( P. X. P. )

  proof
    vx
    vy
    vz
    vw
    vv
    vu
    cpp
    cer
    cnp
    vx
    vy
    vz
    vw
    vv
    vu
    df-enr
    vx
    cv
    #
    vy
    cv
    #
    addcompr
    @0
    @1
    addclpr
    @0
    @1
    vz
    cv
    #
    addasspr
    @0
    @1
    @2
    addcanpr
    ecopover
end
