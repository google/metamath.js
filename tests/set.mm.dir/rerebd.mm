include "cr.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "cc.mm"
include "wb.mm"
include "rereb.mm"
include "syl.mm"
include "mpbird.mm"

theorem rerebd
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )
  assume rerebd.2: |- ( ph -> ( Re ` A ) = A )


  assert |- ( ph -> A e. RR )

  proof
    wph
    cA
    cr
    wcel
    #
    cA
    cre
    cfv
    cA
    wceq
    #
    rerebd.2
    wph
    cA
    cc
    wcel
    @0
    @1
    wb
    recld.1
    cA
    rereb
    syl
    mpbird
end
