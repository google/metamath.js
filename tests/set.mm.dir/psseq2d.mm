include "wceq.mm"
include "wpss.mm"
include "wb.mm"
include "psseq2.mm"
include "syl.mm"

theorem psseq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume psseq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C C. A <-> C C. B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    wpss
    cC
    cB
    wpss
    wb
    psseq1d.1
    cA
    cB
    cC
    psseq2
    syl
end
