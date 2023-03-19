include "cnmcv.mm"
include "cfv.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "c2nd.mm"
include "fveq2i.mm"
include "eqid.mm"
include "nmcvfval.mm"
include "opex.mm"
include "cvv.mm"
include "wcel.mm"
include "cnv.mm"
include "w3a.mm"
include "eqeltrri.mm"
include "nvex.mm"
include "ax-mp.mm"
include "simp3i.mm"
include "op2nd.mm"
include "3eqtrri.mm"

theorem h2hnm
  let cU: class U
  assume h2h.1: |- U = <. <. +h , .h >. , normh >.
  assume h2h.2: |- U e. NrmCVec


  assert |- normh = ( normCV ` U )

  proof
    cU
    cnmcv
    cfv
    cva
    csm
    cop
    #
    cno
    cop
    #
    cnmcv
    cfv
    #
    @1
    c2nd
    cfv
    cno
    cU
    @1
    cnmcv
    h2h.1
    fveq2i
    @1
    @2
    @2
    eqid
    nmcvfval
    @0
    cno
    cva
    csm
    opex
    cva
    cvv
    wcel
    #
    csm
    cvv
    wcel
    #
    cno
    cvv
    wcel
    #
    @1
    cnv
    wcel
    @3
    @4
    @5
    w3a
    cU
    @1
    cnv
    h2h.1
    h2h.2
    eqeltrri
    csm
    cva
    cno
    nvex
    ax-mp
    simp3i
    op2nd
    3eqtrri
end
