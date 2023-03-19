include "wss.mm"
include "sseq2i.mm"
include "sylib.mm"

theorem syl6sseq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl6sseq.1: |- ( ph -> A C_ B )
  assume syl6sseq.2: |- B = C


  assert |- ( ph -> A C_ C )

  proof
    wph
    cA
    cB
    wss
    cA
    cC
    wss
    syl6sseq.1
    cB
    cC
    cA
    syl6sseq.2
    sseq2i
    sylib
end
