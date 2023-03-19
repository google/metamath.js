include "cdm.mm"
include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "crn.mm"
include "cuni.mm"
include "cprb.mm"
include "domprobmeas.mm"
include "syl.mm"
include "measbasedom.mm"
include "sylibr.mm"

theorem probmeasd
  let wph: wff ph
  let cP: class P
  assume probmeasd.1: |- ( ph -> P e. Prob )


  assert |- ( ph -> P e. U. ran measures )

  proof
    wph
    cP
    cP
    cdm
    cmeas
    cfv
    wcel
    #
    cP
    cmeas
    crn
    cuni
    wcel
    wph
    cP
    cprb
    wcel
    @0
    probmeasd.1
    cP
    domprobmeas
    syl
    cP
    measbasedom
    sylibr
end
