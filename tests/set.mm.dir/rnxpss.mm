include "cxp.mm"
include "crn.mm"
include "ccnv.mm"
include "cdm.mm"
include "df-rn.mm"
include "cnvxp.mm"
include "dmeqi.mm"
include "dmxpss.mm"
include "eqsstri.mm"

theorem rnxpss
  let cA: class A
  let cB: class B


  assert |- ran ( A X. B ) C_ B

  proof
    cA
    cB
    cxp
    #
    crn
    @0
    ccnv
    #
    cdm
    #
    cB
    @0
    df-rn
    @2
    cB
    cA
    cxp
    #
    cdm
    cB
    @1
    @3
    cA
    cB
    cnvxp
    dmeqi
    cB
    cA
    dmxpss
    eqsstri
    eqsstri
end
