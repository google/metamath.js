include "ccnv.mm"
include "cdif.mm"
include "c0.mm"
include "cnvdif.mm"
include "wrel.mm"
include "wceq.mm"
include "relcnv.mm"
include "relnonrel.mm"
include "mpbi.mm"
include "eqtri.mm"

theorem cnvnonrel
  let cA: class A


  assert |- `' ( A \ `' `' A ) = (/)

  proof
    cA
    cA
    ccnv
    #
    ccnv
    #
    cdif
    ccnv
    @0
    @1
    ccnv
    cdif
    #
    c0
    cA
    @1
    cnvdif
    @0
    wrel
    @2
    c0
    wceq
    cA
    relcnv
    @0
    relnonrel
    mpbi
    eqtri
end
