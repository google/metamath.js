include "cneg.mm"
include "cr.mm"
include "wcel.mm"
include "cc.mm"
include "wb.mm"
include "negreb.mm"
include "syl.mm"
include "mpbid.mm"

theorem negrebd
  let wph: wff ph
  let cA: class A
  assume negidd.1: |- ( ph -> A e. CC )
  assume negrebd.2: |- ( ph -> -u A e. RR )


  assert |- ( ph -> A e. RR )

  proof
    wph
    cA
    cneg
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    negrebd.2
    wph
    cA
    cc
    wcel
    @0
    @1
    wb
    negidd.1
    cA
    negreb
    syl
    mpbid
end
