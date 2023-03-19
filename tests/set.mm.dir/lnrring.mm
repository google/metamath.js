include "clnr.mm"
include "wcel.mm"
include "crg.mm"
include "crglmod.mm"
include "cfv.mm"
include "clnm.mm"
include "islnr.mm"
include "simplbi.mm"

theorem lnrring
  let cA: class A
  let va: setvar a


  assert |- ( A e. LNoeR -> A e. Ring )

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
    simplbi
end
