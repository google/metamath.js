include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "wb.mm"
include "ltsub2.mm"
include "syl3anc.mm"

theorem ltsub2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )


  assert |- ( ph -> ( A < B <-> ( C - B ) < ( C - A ) ) )

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
    clt
    wbr
    cC
    cB
    cmin
    co
    cC
    cA
    cmin
    co
    clt
    wbr
    wb
    leidd.1
    ltnegd.2
    ltadd1d.3
    cA
    cB
    cC
    ltsub2
    syl3anc
end
