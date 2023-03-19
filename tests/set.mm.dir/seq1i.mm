include "cseq.mm"
include "cfv.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "seq1.mm"
include "ax-mp.mm"
include "syl5eq.mm"

theorem seq1i
  let wph: wff ph
  let cA: class A
  let c.pl: class .+
  let cF: class F
  let cM: class M
  assume seq1i.1: |- M e. ZZ
  assume seq1i.2: |- ( ph -> ( F ` M ) = A )


  assert |- ( ph -> ( seq M ( .+ , F ) ` M ) = A )

  proof
    wph
    cM
    c.pl
    cF
    cM
    cseq
    cfv
    #
    cM
    cF
    cfv
    #
    cA
    cM
    cz
    wcel
    @0
    @1
    wceq
    seq1i.1
    c.pl
    cF
    cM
    seq1
    ax-mp
    seq1i.2
    syl5eq
end
