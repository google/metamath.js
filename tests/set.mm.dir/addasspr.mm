include "cpp.mm"
include "cplq.mm"
include "df-plp.mm"
include "cv.mm"
include "addclnq.mm"
include "dmplp.mm"
include "addclpr.mm"
include "addassnq.mm"
include "genpass.mm"

theorem addasspr
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A +P. B ) +P. C ) = ( A +P. ( B +P. C ) )

  proof
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    cC
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
    vz
    cv
    addclnq
    dmplp
    vf
    cv
    #
    vg
    cv
    #
    addclpr
    @0
    @1
    vh
    cv
    addassnq
    genpass
end
