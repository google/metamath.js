include "wceq.mm"
include "co.mm"
include "oveq.mm"
include "syl.mm"

theorem oveqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume oveq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C A D ) = ( C B D ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cD
    cA
    co
    cC
    cD
    cB
    co
    wceq
    oveq1d.1
    cC
    cD
    cA
    cB
    oveq
    syl
end
