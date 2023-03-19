include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "ccxp.mm"
include "co.mm"
include "wceq.mm"
include "1cxp.mm"
include "syl.mm"

theorem 1cxpd
  let wph: wff ph
  let cA: class A
  assume cxp0d.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( 1 ^c A ) = 1 )

  proof
    wph
    cA
    cc
    wcel
    c1
    cA
    ccxp
    co
    c1
    wceq
    cxp0d.1
    cA
    1cxp
    syl
end
