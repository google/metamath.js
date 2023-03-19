include "wceq.mm"
include "wss.mm"
include "sseq1.mm"
include "anbi1d.mm"

theorem cleq1lem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( ( A C_ C /\ ph ) <-> ( B C_ C /\ ph ) ) )

  proof
    cA
    cB
    wceq
    cA
    cC
    wss
    cB
    cC
    wss
    wph
    cA
    cB
    cC
    sseq1
    anbi1d
end
