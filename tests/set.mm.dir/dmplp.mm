include "cpp.mm"
include "cplq.mm"
include "df-plp.mm"
include "cv.mm"
include "addclnq.mm"
include "genpdm.mm"

theorem dmplp
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cA: class A
  let cB: class B
  let vv: setvar v
  let vu: setvar u


  assert |- dom +P. = ( P. X. P. )

  proof
    vz
    vu
    vv
    vx
    vy
    cpp
    cplq
    vx
    vy
    vz
    vu
    vv
    df-plp
    vu
    cv
    vv
    cv
    addclnq
    genpdm
end
