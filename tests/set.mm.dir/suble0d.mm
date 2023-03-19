include "cr.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "suble0.mm"
include "syl2anc.mm"

theorem suble0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( ( A - B ) <_ 0 <-> A <_ B ) )

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
    cmin
    co
    cc0
    cle
    wbr
    cA
    cB
    cle
    wbr
    wb
    leidd.1
    ltnegd.2
    cA
    cB
    suble0
    syl2anc
end
