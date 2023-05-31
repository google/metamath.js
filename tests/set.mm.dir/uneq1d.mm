include "wceq.mm"
include "cun.mm"
include "uneq1.mm"
include "syl.mm"

theorem uneq1d
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  assume uneq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A u. C ) = ( B u. C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cun
    cB
    cC
    cun
    wceq
    uneq1d.1
    cA
    cB
    cC
    uneq1
    syl
end
