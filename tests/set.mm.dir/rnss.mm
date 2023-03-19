include "wss.mm"
include "ccnv.mm"
include "cdm.mm"
include "crn.mm"
include "cnvss.mm"
include "dmss.mm"
include "syl.mm"
include "df-rn.mm"
include "3sstr4g.mm"

theorem rnss
  let cA: class A
  let cB: class B


  assert |- ( A C_ B -> ran A C_ ran B )

  proof
    cA
    cB
    wss
    #
    cA
    ccnv
    #
    cdm
    #
    cB
    ccnv
    #
    cdm
    #
    cA
    crn
    cB
    crn
    @0
    @1
    @3
    wss
    @2
    @4
    wss
    cA
    cB
    cnvss
    @1
    @3
    dmss
    syl
    cA
    df-rn
    cB
    df-rn
    3sstr4g
end
