include "wceq.mm"
include "cseq.mm"
include "seqeq1.mm"
include "syl.mm"

theorem seqeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cF: class F
  assume seqeqd.1: |- ( ph -> A = B )


  assert |- ( ph -> seq A ( .+ , F ) = seq B ( .+ , F ) )

  proof
    wph
    cA
    cB
    wceq
    c.pl
    cF
    cA
    cseq
    c.pl
    cF
    cB
    cseq
    wceq
    seqeqd.1
    c.pl
    cF
    cA
    cB
    seqeq1
    syl
end
