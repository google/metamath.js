include "chio.mm"
include "ccom.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "df-iop.mm"
include "coeq2i.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "helch.mm"
include "pjfi.mm"
include "hocoi.mm"
include "pjch1.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "rgen.mm"
include "hocofi.mm"
include "hoeqi.mm"
include "mpbi.mm"
include "eqtri.mm"

theorem hoid1i
  let cT: class T
  let vx: setvar x
  assume hoaddid1.1: |- T : ~H --> ~H


  assert |- ( T o. Iop ) = T

  proof
    cT
    chio
    ccom
    cT
    chil
    cpjh
    cfv
    #
    ccom
    #
    cT
    chio
    @0
    cT
    df-iop
    coeq2i
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
    @2
    @0
    cfv
    #
    cT
    cfv
    @4
    @2
    cT
    @0
    hoaddid1.1
    chil
    helch
    pjfi
    #
    hocoi
    @6
    @7
    @2
    cT
    @2
    pjch1
    fveq2d
    eqtrd
    rgen
    vx
    @1
    cT
    cT
    @0
    hoaddid1.1
    @8
    hocofi
    hoaddid1.1
    hoeqi
    mpbi
    eqtri
end
