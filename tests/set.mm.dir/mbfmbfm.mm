include "cdm.mm"
include "csigagen.mm"
include "cfv.mm"
include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "csiga.mm"
include "measbasedom.mm"
include "biimpi.mm"
include "measbase.mm"
include "3syl.mm"
include "ctop.mm"
include "sgsiga.mm"
include "isanmbfm.mm"

theorem mbfmbfm
  let wph: wff ph
  let cF: class F
  let cJ: class J
  let cM: class M
  assume mbfmbfm.1: |- ( ph -> M e. U. ran measures )
  assume mbfmbfm.2: |- ( ph -> J e. Top )
  assume mbfmbfm.3: |- ( ph -> F e. ( dom M MblFnM ( sigaGen ` J ) ) )


  assert |- ( ph -> F e. U. ran MblFnM )

  proof
    wph
    cM
    cdm
    #
    cJ
    csigagen
    cfv
    cF
    wph
    cM
    cmeas
    crn
    cuni
    wcel
    #
    cM
    @0
    cmeas
    cfv
    wcel
    #
    @0
    csiga
    crn
    cuni
    wcel
    mbfmbfm.1
    @1
    @2
    cM
    measbasedom
    biimpi
    @0
    cM
    measbase
    3syl
    wph
    cJ
    ctop
    mbfmbfm.2
    sgsiga
    mbfmbfm.3
    isanmbfm
end
