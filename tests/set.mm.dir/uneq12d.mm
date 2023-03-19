include "wceq.mm"
include "cun.mm"
include "uneq12.mm"
include "syl2anc.mm"

theorem uneq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume uneq1d.1: |- ( ph -> A = B )
  assume uneq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A u. C ) = ( B u. D ) )

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
    cun
    cB
    cD
    cun
    wceq
    uneq1d.1
    uneq12d.2
    cA
    cB
    cC
    cD
    uneq12
    syl2anc
end
