include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "wb.mm"
include "lt0neg2.mm"
include "syl.mm"

theorem lt0neg2d
  let wph: wff ph
  let cA: class A
  assume leidd.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( 0 < A <-> -u A < 0 ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cA
    cneg
    cc0
    clt
    wbr
    wb
    leidd.1
    cA
    lt0neg2
    syl
end
