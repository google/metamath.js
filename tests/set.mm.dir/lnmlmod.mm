include "clnm.mm"
include "wcel.mm"
include "clmod.mm"
include "cv.mm"
include "cress.mm"
include "co.mm"
include "clfig.mm"
include "clss.mm"
include "cfv.mm"
include "wral.mm"
include "eqid.mm"
include "islnm.mm"
include "simplbi.mm"

theorem lnmlmod
  let cM: class M
  let va: setvar a
  let cU: class U
  let cS: class S
  let cR: class R


  assert |- ( M e. LNoeM -> M e. LMod )

  proof
    cM
    clnm
    wcel
    cM
    clmod
    wcel
    cM
    va
    cv
    cress
    co
    clfig
    wcel
    va
    cM
    clss
    cfv
    #
    wral
    @0
    va
    cM
    @0
    eqid
    islnm
    simplbi
end
