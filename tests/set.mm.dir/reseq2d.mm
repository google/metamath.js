include "wceq.mm"
include "cres.mm"
include "reseq2.mm"
include "syl.mm"

theorem reseq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume reseqd.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C |` A ) = ( C |` B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cres
    cC
    cB
    cres
    wceq
    reseqd.1
    cA
    cB
    cC
    reseq2
    syl
end
