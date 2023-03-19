include "cdr.mm"
include "wcel.mm"
include "crglmod.mm"
include "cfv.mm"
include "clmod.mm"
include "csca.mm"
include "clvec.mm"
include "crg.mm"
include "drngring.mm"
include "rlmlmod.mm"
include "syl.mm"
include "rlmsca.mm"
include "id.mm"
include "eqeltrrd.mm"
include "eqid.mm"
include "islvec.mm"
include "sylanbrc.mm"

theorem rlmlvec
  let cR: class R


  assert |- ( R e. DivRing -> ( ringLMod ` R ) e. LVec )

  proof
    cR
    cdr
    wcel
    #
    cR
    crglmod
    cfv
    #
    clmod
    wcel
    #
    @1
    csca
    cfv
    #
    cdr
    wcel
    @1
    clvec
    wcel
    @0
    cR
    crg
    wcel
    @2
    cR
    drngring
    cR
    rlmlmod
    syl
    @0
    cR
    @3
    cdr
    cR
    cdr
    rlmsca
    @0
    id
    eqeltrrd
    @3
    @1
    @3
    eqid
    islvec
    sylanbrc
end
