include "wss.mm"
include "sseq2d.mm"
include "mpbid.mm"

theorem sseqtrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume sseqtrd.1: |- ( ph -> A C_ B )
  assume sseqtrd.2: |- ( ph -> B = C )


  assert |- ( ph -> A C_ C )

  proof
    wph
    cA
    cB
    wss
    cA
    cC
    wss
    sseqtrd.1
    wph
    cB
    cC
    cA
    sseqtrd.2
    sseq2d
    mpbid
end
