include "eqcomd.mm"
include "neeqtrd.mm"

theorem neeqtrrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume neeqtrrd.1: |- ( ph -> A =/= B )
  assume neeqtrrd.2: |- ( ph -> C = B )


  assert |- ( ph -> A =/= C )

  proof
    wph
    cA
    cB
    cC
    neeqtrrd.1
    wph
    cC
    cB
    neeqtrrd.2
    eqcomd
    neeqtrd
end
