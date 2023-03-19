include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "clog.mm"
include "cfv.mm"
include "logcl.mm"
include "syl2anc.mm"

theorem logcld
  let wph: wff ph
  let cX: class X
  assume logcld.1: |- ( ph -> X e. CC )
  assume logcld.2: |- ( ph -> X =/= 0 )


  assert |- ( ph -> ( log ` X ) e. CC )

  proof
    wph
    cX
    cc
    wcel
    cX
    cc0
    wne
    cX
    clog
    cfv
    cc
    wcel
    logcld.1
    logcld.2
    cX
    logcl
    syl2anc
end
