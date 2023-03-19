include "wss.mm"
include "wceq.mm"
include "eqss.mm"
include "sylanbrc.mm"

theorem eqssd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume eqssd.1: |- ( ph -> A C_ B )
  assume eqssd.2: |- ( ph -> B C_ A )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cB
    wss
    cB
    cA
    wss
    cA
    cB
    wceq
    eqssd.1
    eqssd.2
    cA
    cB
    eqss
    sylanbrc
end
