include "cc0.mm"
include "cneg.mm"
include "negeq0d.mm"
include "necon3bid.mm"

theorem negne0bd
  let wph: wff ph
  let cA: class A
  assume negidd.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A =/= 0 <-> -u A =/= 0 ) )

  proof
    wph
    cA
    cc0
    cA
    cneg
    cc0
    wph
    cA
    negidd.1
    negeq0d
    necon3bid
end
