include "c0.mm"
include "csn.mm"
include "ccnv.mm"
include "wceq.mm"
include "crn.mm"
include "cdm.mm"
include "dfdm4.mm"
include "dmsn0.mm"
include "eqtr3i.mm"
include "wrel.mm"
include "wb.mm"
include "relcnv.mm"
include "relrn0.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem cnvsn0



  assert |- `' { (/) } = (/)

  proof
    c0
    csn
    #
    ccnv
    #
    c0
    wceq
    #
    @1
    crn
    #
    c0
    wceq
    #
    @0
    cdm
    @3
    c0
    @0
    dfdm4
    dmsn0
    eqtr3i
    @1
    wrel
    @2
    @4
    wb
    @0
    relcnv
    @1
    relrn0
    ax-mp
    mpbir
end
