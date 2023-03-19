include "cnrg.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "csubrg.mm"
include "crglmod.mm"
include "cnlm.mm"
include "crg.mm"
include "nrgring.mm"
include "eqid.mm"
include "subrgid.mm"
include "syl.mm"
include "rlmval.mm"
include "sranlm.mm"
include "mpdan.mm"

theorem rlmnlm
  let cR: class R


  assert |- ( R e. NrmRing -> ( ringLMod ` R ) e. NrmMod )

  proof
    cR
    cnrg
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
    cnlm
    wcel
    @0
    cR
    crg
    wcel
    @2
    cR
    nrgring
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
    sranlm
    mpdan
end
