include "wss.mm"
include "sseq1d.mm"
include "mpbird.mm"

theorem eqsstrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqsstrd.1: |- ( ph -> A = B )
  assume eqsstrd.2: |- ( ph -> B C_ C )


  assert |- ( ph -> A C_ C )

  proof
    wph
    cA
    cC
    wss
    cB
    cC
    wss
    eqsstrd.2
    wph
    cA
    cB
    cC
    eqsstrd.1
    sseq1d
    mpbird
end
