include "csm.mm"
include "cva.mm"
include "cop.mm"
include "cno.mm"
include "cns.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "eqid.mm"
include "smfval.mm"
include "opex.mm"
include "cvv.mm"
include "wcel.mm"
include "cnv.mm"
include "w3a.mm"
include "eqeltrri.mm"
include "nvex.mm"
include "ax-mp.mm"
include "simp3i.mm"
include "op1st.mm"
include "fveq2i.mm"
include "simp1i.mm"
include "simp2i.mm"
include "op2nd.mm"
include "3eqtrri.mm"
include "eqtr4i.mm"

theorem h2hsm
  let cU: class U
  assume h2h.1: |- U = <. <. +h , .h >. , normh >.
  assume h2h.2: |- U e. NrmCVec


  assert |- .h = ( .sOLD ` U )

  proof
    csm
    cva
    csm
    cop
    #
    cno
    cop
    #
    cns
    cfv
    #
    cU
    cns
    cfv
    @2
    @1
    c1st
    cfv
    #
    c2nd
    cfv
    @0
    c2nd
    cfv
    csm
    @2
    @1
    @2
    eqid
    smfval
    @3
    @0
    c2nd
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
    @4
    @5
    @6
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
    #
    simp3i
    op1st
    fveq2i
    cva
    csm
    @4
    @5
    @6
    @7
    simp1i
    @4
    @5
    @6
    @7
    simp2i
    op2nd
    3eqtrri
    cU
    @1
    cns
    h2h.1
    fveq2i
    eqtr4i
end
