include "cseq.mm"
include "seqeq1d.mm"
include "seqeq2d.mm"
include "seqeq3d.mm"
include "3eqtrd.mm"

theorem seqeq123d
  let wph: wff ph
  let c.pl: class .+
  let cQ: class Q
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  assume seqeq123d.1: |- ( ph -> M = N )
  assume seqeq123d.2: |- ( ph -> .+ = Q )
  assume seqeq123d.3: |- ( ph -> F = G )


  assert |- ( ph -> seq M ( .+ , F ) = seq N ( Q , G ) )

  proof
    wph
    c.pl
    cF
    cM
    cseq
    c.pl
    cF
    cN
    cseq
    cQ
    cF
    cN
    cseq
    cQ
    cG
    cN
    cseq
    wph
    cM
    cN
    c.pl
    cF
    seqeq123d.1
    seqeq1d
    wph
    c.pl
    cQ
    cF
    cN
    seqeq123d.2
    seqeq2d
    wph
    cF
    cG
    cQ
    cN
    seqeq123d.3
    seqeq3d
    3eqtrd
end
