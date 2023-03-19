include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "wb.mm"
include "leneg.mm"
include "syl2anc.mm"

theorem lenegd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A <_ B <-> -u B <_ -u A ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cle
    wbr
    cB
    cneg
    cA
    cneg
    cle
    wbr
    wb
    leidd.1
    ltnegd.2
    cA
    cB
    leneg
    syl2anc
end
