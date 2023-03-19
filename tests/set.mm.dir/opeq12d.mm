include "wceq.mm"
include "cop.mm"
include "opeq12.mm"
include "syl2anc.mm"

theorem opeq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opeq1d.1: |- ( ph -> A = B )
  assume opeq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> <. A , C >. = <. B , D >. )

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
    cop
    cB
    cD
    cop
    wceq
    opeq1d.1
    opeq12d.2
    cA
    cC
    cB
    cD
    opeq12
    syl2anc
end
