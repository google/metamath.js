include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "wb.mm"
include "le0neg2.mm"
include "syl.mm"

theorem le0neg2d
  let wph: wff ph
  let cA: class A
  assume leidd.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( 0 <_ A <-> -u A <_ 0 ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cA
    cneg
    cc0
    cle
    wbr
    wb
    leidd.1
    cA
    le0neg2
    syl
end
