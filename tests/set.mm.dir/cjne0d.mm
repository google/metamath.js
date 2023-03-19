include "cc0.mm"
include "wne.mm"
include "ccj.mm"
include "cfv.mm"
include "cc.mm"
include "wcel.mm"
include "wb.mm"
include "cjne0.mm"
include "syl.mm"
include "mpbid.mm"

theorem cjne0d
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )
  assume cjne0d.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( * ` A ) =/= 0 )

  proof
    wph
    cA
    cc0
    wne
    #
    cA
    ccj
    cfv
    cc0
    wne
    #
    cjne0d.2
    wph
    cA
    cc
    wcel
    @0
    @1
    wb
    recld.1
    cA
    cjne0
    syl
    mpbid
end
