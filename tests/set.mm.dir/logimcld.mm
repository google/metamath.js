include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cpi.mm"
include "cneg.mm"
include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wa.mm"
include "logimcl.mm"
include "syl2anc.mm"

theorem logimcld
  let wph: wff ph
  let cX: class X
  assume logimcld.1: |- ( ph -> X e. CC )
  assume logimcld.2: |- ( ph -> X =/= 0 )


  assert |- ( ph -> ( -u _pi < ( Im ` ( log ` X ) ) /\ ( Im ` ( log ` X ) ) <_ _pi ) )

  proof
    wph
    cX
    cc
    wcel
    cX
    cc0
    wne
    cpi
    cneg
    cX
    clog
    cfv
    cim
    cfv
    #
    clt
    wbr
    @0
    cpi
    cle
    wbr
    wa
    logimcld.1
    logimcld.2
    cX
    logimcl
    syl2anc
end
