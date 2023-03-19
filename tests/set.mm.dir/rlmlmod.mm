include "crg.mm"
include "wcel.mm"
include "crglmod.mm"
include "cfv.mm"
include "cbs.mm"
include "csra.mm"
include "clmod.mm"
include "rlmval.mm"
include "csubrg.mm"
include "eqid.mm"
include "subrgid.mm"
include "sralmod.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem rlmlmod
  let cR: class R


  assert |- ( R e. Ring -> ( ringLMod ` R ) e. LMod )

  proof
    cR
    crg
    wcel
    #
    cR
    crglmod
    cfv
    cR
    cbs
    cfv
    #
    cR
    csra
    cfv
    cfv
    #
    clmod
    cR
    rlmval
    @0
    @1
    cR
    csubrg
    cfv
    wcel
    @2
    clmod
    wcel
    @1
    cR
    @1
    eqid
    subrgid
    @2
    @1
    cR
    @2
    eqid
    sralmod
    syl
    syl5eqel
end
