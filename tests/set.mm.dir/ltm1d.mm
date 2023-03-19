include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "ltm1.mm"
include "syl.mm"

theorem ltm1d
  let wph: wff ph
  let cA: class A
  assume ltp1d.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( A - 1 ) < A )

  proof
    wph
    cA
    cr
    wcel
    cA
    c1
    cmin
    co
    cA
    clt
    wbr
    ltp1d.1
    cA
    ltm1
    syl
end
