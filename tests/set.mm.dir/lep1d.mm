include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "lep1.mm"
include "syl.mm"

theorem lep1d
  let wph: wff ph
  let cA: class A
  assume ltp1d.1: |- ( ph -> A e. RR )


  assert |- ( ph -> A <_ ( A + 1 ) )

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
    cle
    wbr
    ltp1d.1
    cA
    lep1
    syl
end
