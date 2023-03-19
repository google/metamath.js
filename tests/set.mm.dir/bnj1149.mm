include "cvv.mm"
include "wcel.mm"
include "cun.mm"
include "unexg.mm"
include "syl2anc.mm"

theorem bnj1149
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume bnj1149.1: |- ( ph -> A e. _V )
  assume bnj1149.2: |- ( ph -> B e. _V )


  assert |- ( ph -> ( A u. B ) e. _V )

  proof
    wph
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cun
    cvv
    wcel
    bnj1149.1
    bnj1149.2
    cA
    cB
    cvv
    cvv
    unexg
    syl2anc
end
