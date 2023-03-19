include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "ltsub23.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem ltsub23d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )
  assume ltsub23d.4: |- ( ph -> ( A - B ) < C )


  assert |- ( ph -> ( A - C ) < B )

  proof
    wph
    cA
    cB
    cmin
    co
    cC
    clt
    wbr
    #
    cA
    cC
    cmin
    co
    cB
    clt
    wbr
    #
    ltsub23d.4
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
    @0
    @1
    wb
    leidd.1
    ltnegd.2
    ltadd1d.3
    cA
    cB
    cC
    ltsub23
    syl3anc
    mpbid
end
