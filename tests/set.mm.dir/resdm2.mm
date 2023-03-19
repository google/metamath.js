include "ccnv.mm"
include "cdm.mm"
include "cres.mm"
include "rescnvcnv.mm"
include "wrel.mm"
include "wceq.mm"
include "relcnv.mm"
include "resdm.mm"
include "ax-mp.mm"
include "dmcnvcnv.mm"
include "reseq2i.mm"
include "3eqtr3ri.mm"

theorem resdm2
  let cA: class A


  assert |- ( A |` dom A ) = `' `' A

  proof
    cA
    ccnv
    #
    ccnv
    #
    @1
    cdm
    #
    cres
    #
    cA
    @2
    cres
    @1
    cA
    cA
    cdm
    #
    cres
    cA
    @2
    rescnvcnv
    @1
    wrel
    @3
    @1
    wceq
    @0
    relcnv
    @1
    resdm
    ax-mp
    @2
    @4
    cA
    cA
    dmcnvcnv
    reseq2i
    3eqtr3ri
end
