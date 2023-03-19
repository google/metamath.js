include "wceq.mm"
include "cseq.mm"
include "seqeq2.mm"
include "syl.mm"

theorem seqeq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cM: class M
  assume seqeqd.1: |- ( ph -> A = B )


  assert |- ( ph -> seq M ( A , F ) = seq M ( B , F ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cF
    cM
    cseq
    cB
    cF
    cM
    cseq
    wceq
    seqeqd.1
    cA
    cB
    cF
    cM
    seqeq2
    syl
end
