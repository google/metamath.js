include "cr.mm"
include "cc.mm"
include "cn.mm"
include "cpw.mm"
include "cxp.mm"
include "rexpen.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "coprab.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "cmpt2.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "oveq2.mm"
include "oveq12.mm"
include "sylan2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvoprab12v.mm"
include "df-mpt2.mm"
include "eqtr4i.mm"
include "cnref1o.mm"
include "reex.mm"
include "xpex.mm"
include "f1oen.mm"
include "ax-mp.mm"
include "entr3i.mm"
include "rpnnen.mm"

theorem cpnnen
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- CC ~~ ~P NN

  proof
    cr
    cc
    cn
    cpw
    cr
    cr
    cxp
    #
    cr
    cc
    rexpen
    @0
    cc
    vv
    cv
    #
    cr
    wcel
    #
    vw
    cv
    #
    cr
    wcel
    #
    wa
    #
    vz
    cv
    #
    @1
    ci
    @3
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    wa
    #
    vv
    vw
    vz
    coprab
    #
    wf1o
    @0
    cc
    cen
    wbr
    vx
    vy
    @11
    @11
    vx
    cv
    #
    cr
    wcel
    #
    vy
    cv
    #
    cr
    wcel
    #
    wa
    #
    @6
    @12
    ci
    @14
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    vx
    vy
    cr
    cr
    @18
    cmpt2
    @10
    @20
    vv
    vw
    vz
    vx
    vy
    @1
    @12
    wceq
    #
    @3
    @14
    wceq
    #
    wa
    #
    @5
    @16
    @9
    @19
    @21
    @2
    @13
    @22
    @4
    @15
    @1
    @12
    cr
    eleq1
    @3
    @14
    cr
    eleq1
    bi2anan9
    @23
    @8
    @18
    @6
    @22
    @21
    @7
    @17
    wceq
    @8
    @18
    wceq
    @3
    @14
    ci
    cmul
    oveq2
    @1
    @12
    @7
    @17
    caddc
    oveq12
    sylan2
    eqeq2d
    anbi12d
    cbvoprab12v
    vx
    vy
    vz
    cr
    cr
    @18
    df-mpt2
    eqtr4i
    cnref1o
    @0
    cc
    @11
    cr
    cr
    reex
    reex
    xpex
    f1oen
    ax-mp
    entr3i
    rpnnen
    entr3i
end
