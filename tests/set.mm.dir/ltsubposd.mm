include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "wb.mm"
include "ltsubpos.mm"
include "syl2anc.mm"

theorem ltsubposd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( 0 < A <-> ( B - A ) < B ) )

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
    cmin
    co
    cB
    clt
    wbr
    wb
    leidd.1
    ltnegd.2
    cA
    cB
    ltsubpos
    syl2anc
end
