include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "wb.mm"
include "le0neg1.mm"
include "syl.mm"

theorem le0neg1d
  let wph: wff ph
  let cA: class A
  assume leidd.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( A <_ 0 <-> 0 <_ -u A ) )

  proof
    wph
    cA
    cr
    wcel
    cA
    cc0
    cle
    wbr
    cc0
    cA
    cneg
    cle
    wbr
    wb
    leidd.1
    cA
    le0neg1
    syl
end
