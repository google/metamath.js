include "chio.mm"
include "ccom.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "df-iop.mm"
include "coeq1i.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "helch.mm"
include "pjfi.mm"
include "hocoi.mm"
include "ffvelrni.mm"
include "pjch1.mm"
include "syl.mm"
include "eqtrd.mm"
include "rgen.mm"
include "hocofi.mm"
include "hoeqi.mm"
include "mpbi.mm"
include "eqtri.mm"

theorem hoid1ri
  let cT: class T
  let vx: setvar x
  assume hoaddid1.1: |- T : ~H --> ~H


  assert |- ( Iop o. T ) = T

  proof
    chio
    cT
    ccom
    chil
    cpjh
    cfv
    #
    cT
    ccom
    #
    cT
    chio
    @0
    cT
    df-iop
    coeq1i
    vx
    cv
    #
    @1
    cfv
    #
    @2
    cT
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    @1
    cT
    wceq
    @5
    vx
    chil
    @2
    chil
    wcel
    #
    @3
    @4
    @0
    cfv
    #
    @4
    @2
    @0
    cT
    chil
    helch
    pjfi
    #
    hoaddid1.1
    hocoi
    @6
    @4
    chil
    wcel
    @7
    @4
    wceq
    chil
    chil
    @2
    cT
    hoaddid1.1
    ffvelrni
    @4
    pjch1
    syl
    eqtrd
    rgen
    vx
    @1
    cT
    @0
    cT
    @8
    hoaddid1.1
    hocofi
    hoaddid1.1
    hoeqi
    mpbi
    eqtri
end
