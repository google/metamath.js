include "wceq.mm"
include "wss.mm"
include "sseq2.mm"
include "biimpa.mm"
include "sylancl.mm"

theorem syl5sseq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5sseq.1: |- B C_ A
  assume syl5sseq.2: |- ( ph -> A = C )


  assert |- ( ph -> B C_ C )

  proof
    wph
    cA
    cC
    wceq
    #
    cB
    cA
    wss
    #
    cB
    cC
    wss
    #
    syl5sseq.2
    syl5sseq.1
    @0
    @1
    @2
    cA
    cC
    cB
    sseq2
    biimpa
    sylancl
end
