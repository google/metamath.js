include "wceq.mm"
include "con2i.mm"
include "neqned.mm"

theorem necon2ai
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume necon2ai.1: |- ( A = B -> -. ph )


  assert |- ( ph -> A =/= B )

  proof
    wph
    cA
    cB
    cA
    cB
    wceq
    wph
    necon2ai.1
    con2i
    neqned
end
