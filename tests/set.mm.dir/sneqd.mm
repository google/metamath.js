include "wceq.mm"
include "csn.mm"
include "sneq.mm"
include "syl.mm"

theorem sneqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume sneqd.1: |- ( ph -> A = B )


  assert |- ( ph -> { A } = { B } )

  proof
    wph
    cA
    cB
    wceq
    cA
    csn
    cB
    csn
    wceq
    sneqd.1
    cA
    cB
    sneq
    syl
end
