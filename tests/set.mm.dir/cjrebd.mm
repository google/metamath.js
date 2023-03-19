include "cr.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cc.mm"
include "wb.mm"
include "cjreb.mm"
include "syl.mm"
include "mpbird.mm"

theorem cjrebd
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )
  assume cjrebd.2: |- ( ph -> ( * ` A ) = A )


  assert |- ( ph -> A e. RR )

  proof
    wph
    cA
    cr
    wcel
    #
    cA
    ccj
    cfv
    cA
    wceq
    #
    cjrebd.2
    wph
    cA
    cc
    wcel
    @0
    @1
    wb
    recld.1
    cA
    cjreb
    syl
    mpbird
end
