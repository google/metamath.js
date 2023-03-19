include "wbr.mm"
include "wceq.mm"
include "orcd.mm"

theorem frege106d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  assume frege106d.cb: |- ( ph -> A R B )


  assert |- ( ph -> ( A R B \/ A = B ) )

  proof
    wph
    cA
    cB
    cR
    wbr
    cA
    cB
    wceq
    frege106d.cb
    orcd
end
