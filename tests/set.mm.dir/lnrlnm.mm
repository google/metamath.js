include "clnr.mm"
include "wcel.mm"
include "crg.mm"
include "crglmod.mm"
include "cfv.mm"
include "clnm.mm"
include "islnr.mm"
include "simprbi.mm"

theorem lnrlnm
  let cA: class A
  let va: setvar a


  assert |- ( A e. LNoeR -> ( ringLMod ` A ) e. LNoeM )

  proof
    cA
    clnr
    wcel
    cA
    crg
    wcel
    cA
    crglmod
    cfv
    clnm
    wcel
    cA
    islnr
    simprbi
end
