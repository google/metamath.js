include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "wb.mm"
include "ltaddpos2.mm"
include "syl2anc.mm"

theorem ltaddpos2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( 0 < A <-> B < ( A + B ) ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cB
    cA
    cB
    caddc
    co
    clt
    wbr
    wb
    leidd.1
    ltnegd.2
    cA
    cB
    ltaddpos2
    syl2anc
end
