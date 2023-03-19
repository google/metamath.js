include "wceq.mm"
include "wpss.mm"
include "wb.mm"
include "psseq1.mm"
include "syl.mm"

theorem psseq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume psseq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A C. C <-> B C. C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    wpss
    cB
    cC
    wpss
    wb
    psseq1d.1
    cA
    cB
    cC
    psseq1
    syl
end
