include "cmp.mm"
include "cmq.mm"
include "df-mp.mm"
include "cv.mm"
include "mulclnq.mm"
include "ltmnq.mm"
include "mulcomnq.mm"
include "mulclprlem.mm"
include "genpcl.mm"

theorem mulclpr
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h


  assert |- ( ( A e. P. /\ B e. P. ) -> ( A .P. B ) e. P. )

  proof
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    vf
    vg
    vh
    cmp
    cmq
    vw
    vv
    vx
    vy
    vz
    df-mp
    vy
    cv
    #
    vz
    cv
    mulclnq
    vf
    cv
    vg
    cv
    vh
    cv
    ltmnq
    vx
    cv
    @0
    mulcomnq
    vx
    cA
    cB
    vg
    vh
    mulclprlem
    genpcl
end
