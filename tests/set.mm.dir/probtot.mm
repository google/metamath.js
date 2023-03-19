include "cprb.mm"
include "wcel.mm"
include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "cdm.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "elprob.mm"
include "simprbi.mm"

theorem probtot
  let cP: class P


  assert |- ( P e. Prob -> ( P ` U. dom P ) = 1 )

  proof
    cP
    cprb
    wcel
    cP
    cmeas
    crn
    cuni
    wcel
    cP
    cdm
    cuni
    cP
    cfv
    c1
    wceq
    cP
    elprob
    simprbi
end
