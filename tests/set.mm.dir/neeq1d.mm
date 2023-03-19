include "eqeq1d.mm"
include "necon3bid.mm"

theorem neeq1d
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  assume neeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A =/= C <-> B =/= C ) )

  proof
    wph
    cA
    cC
    cB
    cC
    wph
    cA
    cB
    cC
    neeq1d.1
    eqeq1d
    necon3bid
end
