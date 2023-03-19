include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "wb.mm"
include "addge01.mm"
include "syl2anc.mm"

theorem addge01d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( 0 <_ B <-> A <_ ( A + B ) ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    cA
    cA
    cB
    caddc
    co
    cle
    wbr
    wb
    leidd.1
    ltnegd.2
    cA
    cB
    addge01
    syl2anc
end
