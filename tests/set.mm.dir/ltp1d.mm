include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "ltp1.mm"
include "syl.mm"

theorem ltp1d
  let wph: wff ph
  let cA: class A
  assume ltp1d.1: |- ( ph -> A e. RR )


  assert |- ( ph -> A < ( A + 1 ) )

  proof
    wph
    cA
    cr
    wcel
    cA
    cA
    c1
    caddc
    co
    clt
    wbr
    ltp1d.1
    cA
    ltp1
    syl
end
