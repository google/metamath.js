include "cmp.mm"
include "cmq.mm"
include "df-mp.mm"
include "cv.mm"
include "mulclnq.mm"
include "dmmp.mm"
include "mulclpr.mm"
include "mulassnq.mm"
include "genpass.mm"

theorem mulasspr
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


  assert |- ( ( A .P. B ) .P. C ) = ( A .P. ( B .P. C ) )

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
    vz
    cv
    mulclnq
    dmmp
    vf
    cv
    #
    vg
    cv
    #
    mulclpr
    @0
    @1
    vh
    cv
    mulassnq
    genpass
end
