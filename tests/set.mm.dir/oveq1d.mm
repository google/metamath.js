include "wceq.mm"
include "co.mm"
include "oveq1.mm"
include "syl.mm"

theorem oveq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume oveq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A F C ) = ( B F C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cF
    co
    cB
    cC
    cF
    co
    wceq
    oveq1d.1
    cA
    cB
    cC
    cF
    oveq1
    syl
end
