include "ccnv.mm"
include "ccom.mm"
include "cuni.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cnvco.mm"
include "cocnvcnv2.mm"
include "eqtri.mm"
include "unieqi.mm"
include "unidmrn.mm"
include "eqtr3i.mm"
include "wceq.mm"
include "df-rn.mm"
include "eqcomi.mm"
include "dmcoeq.mm"
include "ax-mp.mm"
include "rncoeq.mm"
include "dfdm4.mm"
include "eqtr4i.mm"
include "uneq12i.mm"
include "unidm.mm"
include "3eqtrri.mm"

theorem dfdm2
  let cA: class A


  assert |- dom A = U. U. ( `' A o. A )

  proof
    cA
    ccnv
    #
    cA
    ccom
    #
    cuni
    #
    cuni
    #
    @1
    cdm
    #
    @1
    crn
    #
    cun
    #
    cA
    cdm
    #
    @7
    cun
    @7
    @1
    ccnv
    #
    cuni
    #
    cuni
    @3
    @6
    @9
    @2
    @8
    @1
    @8
    @0
    @0
    ccnv
    ccom
    @1
    @0
    cA
    cnvco
    @0
    cA
    cocnvcnv2
    eqtri
    unieqi
    unieqi
    @1
    unidmrn
    eqtr3i
    @4
    @7
    @5
    @7
    @0
    cdm
    #
    cA
    crn
    #
    wceq
    #
    @4
    @7
    wceq
    @11
    @10
    cA
    df-rn
    eqcomi
    #
    @0
    cA
    dmcoeq
    ax-mp
    @5
    @0
    crn
    #
    @7
    @12
    @5
    @14
    wceq
    @13
    @0
    cA
    rncoeq
    ax-mp
    cA
    dfdm4
    eqtr4i
    uneq12i
    @7
    unidm
    3eqtrri
end
