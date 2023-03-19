include "ccnfld.mm"
include "crglmod.mm"
include "cfv.mm"
include "clmod.mm"
include "crg.mm"
include "wcel.mm"
include "cnring.mm"
include "rlmlmod.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem cnrlmod
  let cC: class C
  assume cnrlmod.c: |- C = ( ringLMod ` CCfld )


  assert |- C e. LMod

  proof
    cC
    ccnfld
    crglmod
    cfv
    #
    clmod
    cnrlmod.c
    ccnfld
    crg
    wcel
    @0
    clmod
    wcel
    cnring
    ccnfld
    rlmlmod
    ax-mp
    eqeltri
end
