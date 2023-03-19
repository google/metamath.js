include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "crn.mm"
include "cdm.mm"
include "ccnv.mm"
include "df-rn.mm"
include "cnvxp.mm"
include "dmeqi.mm"
include "eqtri.mm"
include "dmxp.mm"
include "syl5eq.mm"

theorem rnxp
  let cA: class A
  let cB: class B


  assert |- ( A =/= (/) -> ran ( A X. B ) = B )

  proof
    cA
    c0
    wne
    cA
    cB
    cxp
    #
    crn
    #
    cB
    cA
    cxp
    #
    cdm
    #
    cB
    @1
    @0
    ccnv
    #
    cdm
    @3
    @0
    df-rn
    @4
    @2
    cA
    cB
    cnvxp
    dmeqi
    eqtri
    cB
    cA
    dmxp
    syl5eq
end
