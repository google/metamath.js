include "ccnv.mm"
include "ccom.mm"
include "cdm.mm"
include "crn.mm"
include "dmcoss.mm"
include "df-rn.mm"
include "cnvco.mm"
include "dmeqi.mm"
include "eqtri.mm"
include "3sstr4i.mm"

theorem rncoss
  let cA: class A
  let cB: class B


  assert |- ran ( A o. B ) C_ ran A

  proof
    cB
    ccnv
    #
    cA
    ccnv
    #
    ccom
    #
    cdm
    #
    @1
    cdm
    cA
    cB
    ccom
    #
    crn
    #
    cA
    crn
    @0
    @1
    dmcoss
    @5
    @4
    ccnv
    #
    cdm
    @3
    @4
    df-rn
    @6
    @2
    cA
    cB
    cnvco
    dmeqi
    eqtri
    cA
    df-rn
    3sstr4i
end
