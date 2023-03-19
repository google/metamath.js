include "cbs.mm"
include "cfv.mm"
include "ccnfld.mm"
include "crglmod.mm"
include "cc.mm"
include "fveq2i.mm"
include "cnfldbas.mm"
include "rlmbas.mm"
include "eqtri.mm"
include "eqcomi.mm"

theorem cnrbas
  let cC: class C
  assume cnrlmod.c: |- C = ( ringLMod ` CCfld )


  assert |- ( Base ` C ) = CC

  proof
    cC
    cbs
    cfv
    ccnfld
    crglmod
    cfv
    #
    cbs
    cfv
    #
    cc
    cC
    @0
    cbs
    cnrlmod.c
    fveq2i
    cc
    @1
    cc
    ccnfld
    cbs
    cfv
    @1
    cnfldbas
    ccnfld
    rlmbas
    eqtri
    eqcomi
    eqtri
end
