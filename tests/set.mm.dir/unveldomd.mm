include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "domprobsiga.mm"
include "sgon.mm"
include "baselsiga.mm"
include "4syl.mm"

theorem unveldomd
  let wph: wff ph
  let cP: class P
  assume unveldomd.1: |- ( ph -> P e. Prob )


  assert |- ( ph -> U. dom P e. dom P )

  proof
    wph
    cP
    cprb
    wcel
    cP
    cdm
    #
    csiga
    crn
    cuni
    wcel
    @0
    @0
    cuni
    #
    csiga
    cfv
    wcel
    @1
    @0
    wcel
    unveldomd.1
    cP
    domprobsiga
    @0
    sgon
    @1
    @0
    baselsiga
    4syl
end
