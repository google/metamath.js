include "wpss.mm"
include "psseq1d.mm"
include "psseq2d.mm"
include "bitrd.mm"

theorem psseq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume psseq1d.1: |- ( ph -> A = B )
  assume psseq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A C. C <-> B C. D ) )

  proof
    wph
    cA
    cC
    wpss
    cB
    cC
    wpss
    cB
    cD
    wpss
    wph
    cA
    cB
    cC
    psseq1d.1
    psseq1d
    wph
    cC
    cD
    cB
    psseq12d.2
    psseq2d
    bitrd
end
