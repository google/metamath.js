include "eqeq2d.mm"
include "necon3bid.mm"

theorem neeq2d
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  assume neeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C =/= A <-> C =/= B ) )

  proof
    wph
    cC
    cA
    cC
    cB
    wph
    cA
    cB
    cC
    neeq1d.1
    eqeq2d
    necon3bid
end
