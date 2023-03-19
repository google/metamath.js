include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "wb.mm"
include "posdif.mm"
include "syl2anc.mm"

theorem posdifd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A < B <-> 0 < ( B - A ) ) )

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
    cc0
    cB
    cA
    cmin
    co
    clt
    wbr
    wb
    leidd.1
    ltnegd.2
    cA
    cB
    posdif
    syl2anc
end
