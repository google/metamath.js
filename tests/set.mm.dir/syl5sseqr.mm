include "wss.mm"
include "a1i.mm"
include "sseqtr4d.mm"

theorem syl5sseqr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5sseqr.1: |- B C_ A
  assume syl5sseqr.2: |- ( ph -> C = A )


  assert |- ( ph -> B C_ C )

  proof
    wph
    cB
    cA
    cC
    cB
    cA
    wss
    wph
    syl5sseqr.1
    a1i
    syl5sseqr.2
    sseqtr4d
end
