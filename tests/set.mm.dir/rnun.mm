include "cun.mm"
include "ccnv.mm"
include "cdm.mm"
include "crn.mm"
include "cnvun.mm"
include "dmeqi.mm"
include "dmun.mm"
include "eqtri.mm"
include "df-rn.mm"
include "uneq12i.mm"
include "3eqtr4i.mm"

theorem rnun
  let cA: class A
  let cB: class B


  assert |- ran ( A u. B ) = ( ran A u. ran B )

  proof
    cA
    cB
    cun
    #
    ccnv
    #
    cdm
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
    cun
    #
    @0
    crn
    cA
    crn
    #
    cB
    crn
    #
    cun
    @2
    @3
    @5
    cun
    #
    cdm
    @7
    @1
    @10
    cA
    cB
    cnvun
    dmeqi
    @3
    @5
    dmun
    eqtri
    @0
    df-rn
    @8
    @4
    @9
    @6
    cA
    df-rn
    cB
    df-rn
    uneq12i
    3eqtr4i
end
