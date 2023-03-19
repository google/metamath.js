include "wcel.mm"
include "cop.mm"
include "csn.mm"
include "crn.mm"
include "cdm.mm"
include "ccnv.mm"
include "df-rn.mm"
include "dfdm4.mm"
include "cnvcnvsn.mm"
include "dmeqi.mm"
include "3eqtri.mm"
include "eqtr4i.mm"
include "dmsnopg.mm"
include "syl5eq.mm"

theorem rnsnopg
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ran { <. A , B >. } = { B } )

  proof
    cA
    cV
    wcel
    cA
    cB
    cop
    csn
    #
    crn
    #
    cB
    cA
    cop
    csn
    #
    cdm
    #
    cB
    csn
    @1
    @0
    ccnv
    #
    cdm
    #
    @3
    @0
    df-rn
    @3
    @2
    ccnv
    #
    crn
    @6
    ccnv
    #
    cdm
    @5
    @2
    dfdm4
    @6
    df-rn
    @7
    @4
    cB
    cA
    cnvcnvsn
    dmeqi
    3eqtri
    eqtr4i
    cB
    cA
    cV
    dmsnopg
    syl5eq
end
