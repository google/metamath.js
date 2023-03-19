include "wceq.mm"
include "co.mm"
include "oveq12.mm"
include "syl2anc.mm"

theorem oveq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume oveq1d.1: |- ( ph -> A = B )
  assume oveq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A F C ) = ( B F D ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cF
    co
    cB
    cD
    cF
    co
    wceq
    oveq1d.1
    oveq12d.2
    cA
    cB
    cC
    cD
    cF
    oveq12
    syl2anc
end
