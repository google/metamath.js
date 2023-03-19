include "cr.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "wb.mm"
include "lesubadd.mm"
include "syl3anc.mm"

theorem lesubaddd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )


  assert |- ( ph -> ( ( A - B ) <_ C <-> A <_ ( C + B ) ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cC
    cr
    wcel
    cA
    cB
    cmin
    co
    cC
    cle
    wbr
    cA
    cC
    cB
    caddc
    co
    cle
    wbr
    wb
    leidd.1
    ltnegd.2
    ltadd1d.3
    cA
    cB
    cC
    lesubadd
    syl3anc
end
