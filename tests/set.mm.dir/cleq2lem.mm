include "wceq.mm"
include "wss.mm"
include "sseq2.mm"
include "anbi12d.mm"

theorem cleq2lem
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cR: class R
  assume cleq2lem.b: |- ( A = B -> ( ph <-> ps ) )


  assert |- ( A = B -> ( ( R C_ A /\ ph ) <-> ( R C_ B /\ ps ) ) )

  proof
    cA
    cB
    wceq
    cR
    cA
    wss
    cR
    cB
    wss
    wph
    wps
    cA
    cB
    cR
    sseq2
    cleq2lem.b
    anbi12d
end
