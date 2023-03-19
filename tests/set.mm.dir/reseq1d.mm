include "wceq.mm"
include "cres.mm"
include "reseq1.mm"
include "syl.mm"

theorem reseq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume reseqd.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A |` C ) = ( B |` C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cres
    cB
    cC
    cres
    wceq
    reseqd.1
    cA
    cB
    cC
    reseq1
    syl
end
