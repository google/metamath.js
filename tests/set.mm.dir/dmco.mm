include "ccom.mm"
include "cdm.mm"
include "ccnv.mm"
include "crn.mm"
include "cima.mm"
include "dfdm4.mm"
include "cnvco.mm"
include "rneqi.mm"
include "rnco2.mm"
include "imaeq2i.mm"
include "eqtr4i.mm"
include "3eqtri.mm"

theorem dmco
  let cA: class A
  let cB: class B


  assert |- dom ( A o. B ) = ( `' B " dom A )

  proof
    cA
    cB
    ccom
    #
    cdm
    @0
    ccnv
    #
    crn
    cB
    ccnv
    #
    cA
    ccnv
    #
    ccom
    #
    crn
    #
    @2
    cA
    cdm
    #
    cima
    #
    @0
    dfdm4
    @1
    @4
    cA
    cB
    cnvco
    rneqi
    @5
    @2
    @3
    crn
    #
    cima
    @7
    @2
    @3
    rnco2
    @6
    @8
    @2
    cA
    dfdm4
    imaeq2i
    eqtr4i
    3eqtri
end
