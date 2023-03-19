include "wceq.mm"
include "neii.mm"
include "mtbir.mm"

theorem nemtbir
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume nemtbir.1: |- A =/= B
  assume nemtbir.2: |- ( ph <-> A = B )


  assert |- -. ph

  proof
    wph
    cA
    cB
    wceq
    cA
    cB
    nemtbir.1
    neii
    nemtbir.2
    mtbir
end
