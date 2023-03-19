include "wceq.mm"
include "wb.mm"
include "eqeq12.mm"
include "syl2anc.mm"

theorem eqeq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume eqeq12d.1: |- ( ph -> A = B )
  assume eqeq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A = C <-> B = D ) )

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
    wceq
    cB
    cD
    wceq
    wb
    eqeq12d.1
    eqeq12d.2
    cA
    cB
    cC
    cD
    eqeq12
    syl2anc
end
