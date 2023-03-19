include "ccnfld.mm"
include "cnrg.mm"
include "wcel.mm"
include "cdr.mm"
include "cnvc.mm"
include "cnnrg.mm"
include "cndrng.mm"
include "wa.mm"
include "crglmod.mm"
include "cfv.mm"
include "rlmnvc.mm"
include "syl5eqel.mm"
include "mp2an.mm"

theorem cnrnvc
  let cC: class C
  assume cnrnvc.c: |- C = ( ringLMod ` CCfld )


  assert |- C e. NrmVec

  proof
    ccnfld
    cnrg
    wcel
    #
    ccnfld
    cdr
    wcel
    #
    cC
    cnvc
    wcel
    cnnrg
    cndrng
    @0
    @1
    wa
    cC
    ccnfld
    crglmod
    cfv
    cnvc
    cnrnvc.c
    ccnfld
    rlmnvc
    syl5eqel
    mp2an
end
