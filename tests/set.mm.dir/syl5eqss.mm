include "wss.mm"
include "sseq1i.mm"
include "sylibr.mm"

theorem syl5eqss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5eqss.1: |- A = B
  assume syl5eqss.2: |- ( ph -> B C_ C )


  assert |- ( ph -> A C_ C )

  proof
    wph
    cB
    cC
    wss
    cA
    cC
    wss
    syl5eqss.2
    cA
    cB
    cC
    syl5eqss.1
    sseq1i
    sylibr
end
