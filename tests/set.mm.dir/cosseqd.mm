include "wceq.mm"
include "ccoss.mm"
include "cosseq.mm"
include "syl.mm"

theorem cosseqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume cosseqd.1: |- ( ph -> A = B )


  assert |- ( ph -> ,~ A = ,~ B )

  proof
    wph
    cA
    cB
    wceq
    cA
    ccoss
    cB
    ccoss
    wceq
    cosseqd.1
    cA
    cB
    cosseq
    syl
end
