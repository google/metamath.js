include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "ccxp.mm"
include "co.mm"
include "wceq.mm"
include "cxp1.mm"
include "syl.mm"

theorem cxp1d
  let wph: wff ph
  let cA: class A
  assume cxp0d.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A ^c 1 ) = A )

  proof
    wph
    cA
    cc
    wcel
    cA
    c1
    ccxp
    co
    cA
    wceq
    cxp0d.1
    cA
    cxp1
    syl
end
