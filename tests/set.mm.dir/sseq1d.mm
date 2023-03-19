include "wceq.mm"
include "wss.mm"
include "wb.mm"
include "sseq1.mm"
include "syl.mm"

theorem sseq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume sseq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A C_ C <-> B C_ C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    wss
    cB
    cC
    wss
    wb
    sseq1d.1
    cA
    cB
    cC
    sseq1
    syl
end
