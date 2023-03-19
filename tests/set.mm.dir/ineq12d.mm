include "wceq.mm"
include "cin.mm"
include "ineq12.mm"
include "syl2anc.mm"

theorem ineq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ineq1d.1: |- ( ph -> A = B )
  assume ineq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A i^i C ) = ( B i^i D ) )

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
    cin
    cB
    cD
    cin
    wceq
    ineq1d.1
    ineq12d.2
    cA
    cB
    cC
    cD
    ineq12
    syl2anc
end
