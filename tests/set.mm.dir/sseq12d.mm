include "wss.mm"
include "sseq1d.mm"
include "sseq2d.mm"
include "bitrd.mm"

theorem sseq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume sseq1d.1: |- ( ph -> A = B )
  assume sseq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A C_ C <-> B C_ D ) )

  proof
    wph
    cA
    cC
    wss
    cB
    cC
    wss
    cB
    cD
    wss
    wph
    cA
    cB
    cC
    sseq1d.1
    sseq1d
    wph
    cC
    cD
    cB
    sseq12d.2
    sseq2d
    bitrd
end
