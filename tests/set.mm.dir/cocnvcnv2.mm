include "ccnv.mm"
include "ccom.mm"
include "cvv.mm"
include "cres.mm"
include "cnvcnv2.mm"
include "coeq2i.mm"
include "resco.mm"
include "wrel.mm"
include "wceq.mm"
include "relco.mm"
include "dfrel3.mm"
include "mpbi.mm"
include "3eqtr2i.mm"

theorem cocnvcnv2
  let cA: class A
  let cB: class B


  assert |- ( A o. `' `' B ) = ( A o. B )

  proof
    cA
    cB
    ccnv
    ccnv
    #
    ccom
    cA
    cB
    cvv
    cres
    #
    ccom
    cA
    cB
    ccom
    #
    cvv
    cres
    #
    @2
    @0
    @1
    cA
    cB
    cnvcnv2
    coeq2i
    cA
    cB
    cvv
    resco
    @2
    wrel
    @3
    @2
    wceq
    cA
    cB
    relco
    @2
    dfrel3
    mpbi
    3eqtr2i
end
