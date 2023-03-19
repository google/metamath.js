include "ccnfld.mm"
include "cnm.mm"
include "cfv.mm"
include "crglmod.mm"
include "cabs.mm"
include "rlmnm.mm"
include "cnfldnm.mm"
include "fveq2i.mm"
include "3eqtr4ri.mm"

theorem cnnm
  let cC: class C
  assume cnrnvc.c: |- C = ( ringLMod ` CCfld )


  assert |- ( norm ` C ) = abs

  proof
    ccnfld
    cnm
    cfv
    ccnfld
    crglmod
    cfv
    #
    cnm
    cfv
    cabs
    cC
    cnm
    cfv
    ccnfld
    rlmnm
    cnfldnm
    cC
    @0
    cnm
    cnrnvc.c
    fveq2i
    3eqtr4ri
end
