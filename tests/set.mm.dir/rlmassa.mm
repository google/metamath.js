include "ccrg.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "csubrg.mm"
include "crglmod.mm"
include "casa.mm"
include "crg.mm"
include "crngring.mm"
include "eqid.mm"
include "subrgid.mm"
include "syl.mm"
include "rlmval.mm"
include "sraassa.mm"
include "mpdan.mm"

theorem rlmassa
  let cR: class R


  assert |- ( R e. CRing -> ( ringLMod ` R ) e. AssAlg )

  proof
    cR
    ccrg
    wcel
    #
    cR
    cbs
    cfv
    #
    cR
    csubrg
    cfv
    wcel
    #
    cR
    crglmod
    cfv
    #
    casa
    wcel
    @0
    cR
    crg
    wcel
    @2
    cR
    crngring
    @1
    cR
    @1
    eqid
    subrgid
    syl
    @3
    @1
    cR
    cR
    rlmval
    sraassa
    mpdan
end
