include "cres.mm"
include "ccnv.mm"
include "wrel.mm"
include "wceq.mm"
include "relres.mm"
include "dfrel2.mm"
include "mpbi.mm"
include "rescnvcnv.mm"
include "eqtr4i.mm"

theorem cnvcnvres
  let cA: class A
  let cB: class B


  assert |- `' `' ( A |` B ) = ( `' `' A |` B )

  proof
    cA
    cB
    cres
    #
    ccnv
    ccnv
    #
    @0
    cA
    ccnv
    ccnv
    cB
    cres
    @0
    wrel
    @1
    @0
    wceq
    cA
    cB
    relres
    @0
    dfrel2
    mpbi
    cA
    cB
    rescnvcnv
    eqtr4i
end
