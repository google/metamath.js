include "cpp.mm"
include "cplq.mm"
include "df-plp.mm"
include "cv.mm"
include "addclnq.mm"
include "ltanq.mm"
include "addcomnq.mm"
include "addclprlem2.mm"
include "genpcl.mm"

theorem addclpr
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


  assert |- ( ( A e. P. /\ B e. P. ) -> ( A +P. B ) e. P. )

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
    cpp
    cplq
    vw
    vv
    vx
    vy
    vz
    df-plp
    vy
    cv
    #
    vz
    cv
    addclnq
    vf
    cv
    vg
    cv
    vh
    cv
    ltanq
    vx
    cv
    @0
    addcomnq
    vx
    cA
    cB
    vg
    vh
    addclprlem2
    genpcl
end
