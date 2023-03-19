include "cr.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "wb.mm"
include "ltaddsub.mm"
include "syl3anc.mm"

theorem ltaddsubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )


  assert |- ( ph -> ( ( A + B ) < C <-> A < ( C - B ) ) )

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
    caddc
    co
    cC
    clt
    wbr
    cA
    cC
    cB
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
    ltaddsub
    syl3anc
end
