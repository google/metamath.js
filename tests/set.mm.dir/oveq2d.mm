include "wceq.mm"
include "co.mm"
include "oveq2.mm"
include "syl.mm"

theorem oveq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume oveq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C F A ) = ( C F B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cF
    co
    cC
    cB
    cF
    co
    wceq
    oveq1d.1
    cA
    cB
    cC
    cF
    oveq2
    syl
end
