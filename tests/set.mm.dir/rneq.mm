include "wceq.mm"
include "ccnv.mm"
include "cdm.mm"
include "crn.mm"
include "cnveq.mm"
include "dmeqd.mm"
include "df-rn.mm"
include "3eqtr4g.mm"

theorem rneq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> ran A = ran B )

  proof
    cA
    cB
    wceq
    #
    cA
    ccnv
    #
    cdm
    cB
    ccnv
    #
    cdm
    cA
    crn
    cB
    crn
    @0
    @1
    @2
    cA
    cB
    cnveq
    dmeqd
    cA
    df-rn
    cB
    df-rn
    3eqtr4g
end
