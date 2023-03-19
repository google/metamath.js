include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "ltsub13.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem ltsub13d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )
  assume ltsub13d.4: |- ( ph -> A < ( B - C ) )


  assert |- ( ph -> C < ( B - A ) )

  proof
    wph
    cA
    cB
    cC
    cmin
    co
    clt
    wbr
    #
    cC
    cB
    cA
    cmin
    co
    clt
    wbr
    #
    ltsub13d.4
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
    ltsub13
    syl3anc
    mpbid
end
