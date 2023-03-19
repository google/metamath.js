include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "ccxp.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cxp0.mm"
include "syl.mm"

theorem cxp0d
  let wph: wff ph
  let cA: class A
  assume cxp0d.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A ^c 0 ) = 1 )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    ccxp
    co
    c1
    wceq
    cxp0d.1
    cA
    cxp0
    syl
end
