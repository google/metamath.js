include "eqeq12d.mm"
include "necon3bid.mm"

theorem neeq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume neeq1d.1: |- ( ph -> A = B )
  assume neeq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A =/= C <-> B =/= D ) )

  proof
    wph
    cA
    cC
    cB
    cD
    wph
    cA
    cB
    cC
    cD
    neeq1d.1
    neeq12d.2
    eqeq12d
    necon3bid
end
