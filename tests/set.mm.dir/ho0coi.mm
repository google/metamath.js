include "cv.mm"
include "ch0o.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "c0v.mm"
include "ffvelrni.mm"
include "ho0val.mm"
include "syl.mm"
include "ho0f.mm"
include "hocoi.mm"
include "3eqtr4d.mm"
include "rgen.mm"
include "hocofi.mm"
include "hoeqi.mm"
include "mpbi.mm"

theorem ho0coi
  let cT: class T
  let vx: setvar x
  assume hoaddid1.1: |- T : ~H --> ~H


  assert |- ( 0hop o. T ) = 0hop

  proof
    vx
    cv
    #
    ch0o
    cT
    ccom
    #
    cfv
    #
    @0
    ch0o
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @1
    ch0o
    wceq
    @4
    vx
    chil
    @0
    chil
    wcel
    #
    @0
    cT
    cfv
    #
    ch0o
    cfv
    #
    c0v
    @2
    @3
    @5
    @6
    chil
    wcel
    @7
    c0v
    wceq
    chil
    chil
    @0
    cT
    hoaddid1.1
    ffvelrni
    @6
    ho0val
    syl
    @0
    ch0o
    cT
    ho0f
    hoaddid1.1
    hocoi
    @0
    ho0val
    3eqtr4d
    rgen
    vx
    @1
    ch0o
    ch0o
    cT
    ho0f
    hoaddid1.1
    hocofi
    ho0f
    hoeqi
    mpbi
end
