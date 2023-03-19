include "gtned.mm"
include "necomd.mm"

theorem ltned
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltned.2: |- ( ph -> A < B )


  assert |- ( ph -> A =/= B )

  proof
    wph
    cB
    cA
    wph
    cA
    cB
    ltd.1
    ltned.2
    gtned
    necomd
end
