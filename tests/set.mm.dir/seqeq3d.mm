include "wceq.mm"
include "cseq.mm"
include "seqeq3.mm"
include "syl.mm"

theorem seqeq3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cM: class M
  assume seqeqd.1: |- ( ph -> A = B )


  assert |- ( ph -> seq M ( .+ , A ) = seq M ( .+ , B ) )

  proof
    wph
    cA
    cB
    wceq
    c.pl
    cA
    cM
    cseq
    c.pl
    cB
    cM
    cseq
    wceq
    seqeqd.1
    c.pl
    cA
    cB
    cM
    seqeq3
    syl
end
