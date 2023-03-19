include "cr.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "wb.mm"
include "ltsubadd.mm"
include "syl3anc.mm"

theorem ltsubaddd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )


  assert |- ( ph -> ( ( A - B ) < C <-> A < ( C + B ) ) )

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
    clt
    wbr
    cA
    cC
    cB
    caddc
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
    ltsubadd
    syl3anc
end
