include "eqcomi.mm"
include "syl6sseq.mm"

theorem syl6sseqr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl6ssr.1: |- ( ph -> A C_ B )
  assume syl6ssr.2: |- C = B


  assert |- ( ph -> A C_ C )

  proof
    wph
    cA
    cB
    cC
    syl6ssr.1
    cC
    cB
    syl6ssr.2
    eqcomi
    syl6sseq
end
