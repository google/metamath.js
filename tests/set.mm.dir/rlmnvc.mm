include "cnrg.mm"
include "wcel.mm"
include "crglmod.mm"
include "cfv.mm"
include "cnlm.mm"
include "clvec.mm"
include "cnvc.mm"
include "cdr.mm"
include "rlmnlm.mm"
include "rlmlvec.mm"
include "wa.mm"
include "isnvc.mm"
include "biimpri.mm"
include "syl2an.mm"

theorem rlmnvc
  let cR: class R


  assert |- ( ( R e. NrmRing /\ R e. DivRing ) -> ( ringLMod ` R ) e. NrmVec )

  proof
    cR
    cnrg
    wcel
    cR
    crglmod
    cfv
    #
    cnlm
    wcel
    #
    @0
    clvec
    wcel
    #
    @0
    cnvc
    wcel
    #
    cR
    cdr
    wcel
    cR
    rlmnlm
    cR
    rlmlvec
    @3
    @1
    @2
    wa
    @0
    isnvc
    biimpri
    syl2an
end
