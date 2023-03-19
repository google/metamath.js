include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "cmeas.mm"
include "cfv.mm"
include "c0.mm"
include "cc0.mm"
include "wceq.mm"
include "domprobmeas.mm"
include "measvnul.mm"
include "syl.mm"

theorem probnul
  let cP: class P


  assert |- ( P e. Prob -> ( P ` (/) ) = 0 )

  proof
    cP
    cprb
    wcel
    cP
    cP
    cdm
    #
    cmeas
    cfv
    wcel
    c0
    cP
    cfv
    cc0
    wceq
    cP
    domprobmeas
    @0
    cP
    measvnul
    syl
end
