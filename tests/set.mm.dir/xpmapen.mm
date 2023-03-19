include "cv.mm"
include "cfv.mm"
include "c1st.mm"
include "cmpt.mm"
include "c2nd.mm"
include "cop.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "opeq12d.mm"
include "xpmapenlem.mm"

theorem xpmapen
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume xpmapen.1: |- A e. _V
  assume xpmapen.2: |- B e. _V
  assume xpmapen.3: |- C e. _V


  assert |- ( ( A X. B ) ^m C ) ~~ ( ( A ^m C ) X. ( B ^m C ) )

  proof
    vx
    vy
    vz
    cA
    cB
    cC
    vw
    cC
    vw
    cv
    #
    vx
    cv
    #
    cfv
    #
    c1st
    cfv
    #
    cmpt
    vw
    cC
    @2
    c2nd
    cfv
    #
    cmpt
    vw
    cC
    @0
    vy
    cv
    #
    c1st
    cfv
    #
    cfv
    #
    @0
    @5
    c2nd
    cfv
    #
    cfv
    #
    cop
    #
    cmpt
    xpmapen.1
    xpmapen.2
    xpmapen.3
    vw
    vz
    cC
    @3
    vz
    cv
    #
    @1
    cfv
    #
    c1st
    cfv
    vw
    vz
    weq
    #
    @2
    @12
    c1st
    @0
    @11
    @1
    fveq2
    #
    fveq2d
    cbvmptv
    vw
    vz
    cC
    @4
    @12
    c2nd
    cfv
    @13
    @2
    @12
    c2nd
    @14
    fveq2d
    cbvmptv
    vw
    vz
    cC
    @10
    @11
    @6
    cfv
    #
    @11
    @8
    cfv
    #
    cop
    @13
    @7
    @15
    @9
    @16
    @0
    @11
    @6
    fveq2
    @0
    @11
    @8
    fveq2
    opeq12d
    cbvmptv
    xpmapenlem
end
