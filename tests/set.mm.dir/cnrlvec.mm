include "ccnfld.mm"
include "crglmod.mm"
include "cfv.mm"
include "clvec.mm"
include "cdr.mm"
include "wcel.mm"
include "cndrng.mm"
include "rlmlvec.mm"
include "ax-mp.mm"
include "eqeltri.mm"

theorem cnrlvec
  let cC: class C
  assume cnrlmod.c: |- C = ( ringLMod ` CCfld )


  assert |- C e. LVec

  proof
    cC
    ccnfld
    crglmod
    cfv
    #
    clvec
    cnrlmod.c
    ccnfld
    cdr
    wcel
    @0
    clvec
    wcel
    cndrng
    ccnfld
    rlmlvec
    ax-mp
    eqeltri
end
