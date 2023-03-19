include "cfn.mm"
include "wcel.mm"
include "crn.mm"
include "ccnv.mm"
include "cdm.mm"
include "df-rn.mm"
include "cnvfi.mm"
include "dmfi.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem rnfi
  let cA: class A


  assert |- ( A e. Fin -> ran A e. Fin )

  proof
    cA
    cfn
    wcel
    #
    cA
    crn
    cA
    ccnv
    #
    cdm
    #
    cfn
    cA
    df-rn
    @0
    @1
    cfn
    wcel
    @2
    cfn
    wcel
    cA
    cnvfi
    @1
    dmfi
    syl
    syl5eqel
end
