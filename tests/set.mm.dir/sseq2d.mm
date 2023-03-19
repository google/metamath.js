include "wceq.mm"
include "wss.mm"
include "wb.mm"
include "sseq2.mm"
include "syl.mm"

theorem sseq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume sseq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C C_ A <-> C C_ B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    wss
    cC
    cB
    wss
    wb
    sseq1d.1
    cA
    cB
    cC
    sseq2
    syl
end
