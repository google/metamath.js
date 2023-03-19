include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "wb.mm"
include "lt0neg1.mm"
include "syl.mm"

theorem lt0neg1d
  let wph: wff ph
  let cA: class A
  assume leidd.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( A < 0 <-> 0 < -u A ) )

  proof
    wph
    cA
    cr
    wcel
    cA
    cc0
    clt
    wbr
    cc0
    cA
    cneg
    clt
    wbr
    wb
    leidd.1
    cA
    lt0neg1
    syl
end
