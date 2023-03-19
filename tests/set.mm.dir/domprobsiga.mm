include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "cmeas.mm"
include "cfv.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "domprobmeas.mm"
include "measbase.mm"
include "syl.mm"

theorem domprobsiga
  let cP: class P


  assert |- ( P e. Prob -> dom P e. U. ran sigAlgebra )

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
    @0
    csiga
    crn
    cuni
    wcel
    cP
    domprobmeas
    @0
    cP
    measbase
    syl
end
