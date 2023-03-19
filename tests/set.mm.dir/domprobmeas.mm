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
include "simplbi.mm"
include "measbasedom.mm"
include "sylib.mm"

theorem domprobmeas
  let cP: class P


  assert |- ( P e. Prob -> P e. ( measures ` dom P ) )

  proof
    cP
    cprb
    wcel
    #
    cP
    cmeas
    crn
    cuni
    wcel
    #
    cP
    cP
    cdm
    #
    cmeas
    cfv
    wcel
    @0
    @1
    @2
    cuni
    cP
    cfv
    c1
    wceq
    cP
    elprob
    simplbi
    cP
    measbasedom
    sylib
end
