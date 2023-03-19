include "cres.mm"
include "reseq1d.mm"
include "reseq2d.mm"
include "eqtrd.mm"

theorem reseq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume reseqd.1: |- ( ph -> A = B )
  assume reseqd.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A |` C ) = ( B |` D ) )

  proof
    wph
    cA
    cC
    cres
    cB
    cC
    cres
    cB
    cD
    cres
    wph
    cA
    cB
    cC
    reseqd.1
    reseq1d
    wph
    cC
    cD
    cB
    reseqd.2
    reseq2d
    eqtrd
end
