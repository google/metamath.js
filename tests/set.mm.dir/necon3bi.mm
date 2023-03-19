include "wn.mm"
include "wceq.mm"
include "con3i.mm"
include "neqned.mm"

theorem necon3bi
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume necon3bi.1: |- ( A = B -> ph )


  assert |- ( -. ph -> A =/= B )

  proof
    wph
    wn
    cA
    cB
    cA
    cB
    wceq
    wph
    necon3bi.1
    con3i
    neqned
end
