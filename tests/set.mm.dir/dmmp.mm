include "cmp.mm"
include "cmq.mm"
include "df-mp.mm"
include "cv.mm"
include "mulclnq.mm"
include "genpdm.mm"

theorem dmmp
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


  assert |- dom .P. = ( P. X. P. )

  proof
    vz
    vu
    vv
    vx
    vy
    cmp
    cmq
    vx
    vy
    vz
    vu
    vv
    df-mp
    vu
    cv
    vv
    cv
    mulclnq
    genpdm
end
