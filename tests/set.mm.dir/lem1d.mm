include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "lem1.mm"
include "syl.mm"

theorem lem1d
  let wph: wff ph
  let cA: class A
  assume ltp1d.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( A - 1 ) <_ A )

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
    cle
    wbr
    ltp1d.1
    cA
    lem1
    syl
end
