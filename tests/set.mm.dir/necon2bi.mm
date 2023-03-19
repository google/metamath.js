include "wceq.mm"
include "neneqd.mm"
include "con2i.mm"

theorem necon2bi
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume necon2bi.1: |- ( ph -> A =/= B )


  assert |- ( A = B -> -. ph )

  proof
    wph
    cA
    cB
    wceq
    wph
    cA
    cB
    necon2bi.1
    neneqd
    con2i
end
