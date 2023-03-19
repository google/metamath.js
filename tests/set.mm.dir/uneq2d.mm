include "wceq.mm"
include "cun.mm"
include "uneq2.mm"
include "syl.mm"

theorem uneq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume uneq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C u. A ) = ( C u. B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cun
    cC
    cB
    cun
    wceq
    uneq1d.1
    cA
    cB
    cC
    uneq2
    syl
end
