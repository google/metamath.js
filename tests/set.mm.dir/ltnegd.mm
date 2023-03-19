include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "wb.mm"
include "ltneg.mm"
include "syl2anc.mm"

theorem ltnegd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A < B <-> -u B < -u A ) )

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
    clt
    wbr
    cB
    cneg
    cA
    cneg
    clt
    wbr
    wb
    leidd.1
    ltnegd.2
    cA
    cB
    ltneg
    syl2anc
end
