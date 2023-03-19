include "cv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "cen.mm"
include "wbr.mm"
include "wo.mm"
include "w3a.mm"
include "cvv.mm"
include "wi.mm"
include "simpl.mm"
include "ralimi.mm"
include "weq.mm"
include "pweq.mm"
include "sseq1d.mm"
include "rspccv.mm"
include "syl.mm"
include "anim2i.mm"
include "3adant3.mm"
include "pm3.35.mm"
include "vex.mm"
include "ssex.mm"
include "3syl.mm"
include "axgroth5.mm"
include "exlimiiv.mm"

theorem grothpwex
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u


  assert |- ~P x e. _V

  proof
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    vz
    cv
    #
    cpw
    #
    @1
    wss
    #
    @4
    vw
    cv
    wss
    vw
    @1
    wrex
    #
    wa
    #
    vz
    @1
    wral
    #
    @3
    @1
    cen
    wbr
    @3
    @1
    wcel
    wo
    vz
    @1
    cpw
    wral
    #
    w3a
    #
    @0
    cpw
    #
    cvv
    wcel
    #
    vy
    @10
    @2
    @2
    @11
    @1
    wss
    #
    wi
    #
    wa
    #
    @13
    @12
    @2
    @8
    @15
    @9
    @8
    @14
    @2
    @8
    @5
    vz
    @1
    wral
    @14
    @7
    @5
    vz
    @1
    @5
    @6
    simpl
    ralimi
    @5
    @13
    vz
    @0
    @1
    vz
    vx
    weq
    @4
    @11
    @1
    @3
    @0
    pweq
    sseq1d
    rspccv
    syl
    anim2i
    3adant3
    @2
    @13
    pm3.35
    @11
    @1
    vy
    vex
    ssex
    3syl
    vx
    vy
    vz
    vw
    axgroth5
    exlimiiv
end
