include "ccnv.mm"
include "cdm.mm"
include "crn.mm"
include "wceq.mm"
include "ccom.mm"
include "dmcoeq.mm"
include "eqcom.mm"
include "df-rn.mm"
include "dfdm4.mm"
include "eqeq12i.mm"
include "bitri.mm"
include "cnvco.mm"
include "dmeqi.mm"
include "eqtri.mm"
include "3imtr4i.mm"

theorem rncoeq
  let cA: class A
  let cB: class B


  assert |- ( dom A = ran B -> ran ( A o. B ) = ran A )

  proof
    cB
    ccnv
    #
    cdm
    #
    cA
    ccnv
    #
    crn
    #
    wceq
    #
    @0
    @2
    ccom
    #
    cdm
    #
    @2
    cdm
    #
    wceq
    cA
    cdm
    #
    cB
    crn
    #
    wceq
    #
    cA
    cB
    ccom
    #
    crn
    #
    cA
    crn
    #
    wceq
    @0
    @2
    dmcoeq
    @10
    @9
    @8
    wceq
    @4
    @8
    @9
    eqcom
    @9
    @1
    @8
    @3
    cB
    df-rn
    cA
    dfdm4
    eqeq12i
    bitri
    @12
    @6
    @13
    @7
    @12
    @11
    ccnv
    #
    cdm
    @6
    @11
    df-rn
    @14
    @5
    cA
    cB
    cnvco
    dmeqi
    eqtri
    cA
    df-rn
    eqeq12i
    3imtr4i
end
