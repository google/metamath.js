include "eqcomd.mm"
include "eqnetrd.mm"

theorem eqnetrrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqnetrrd.1: |- ( ph -> A = B )
  assume eqnetrrd.2: |- ( ph -> A =/= C )


  assert |- ( ph -> B =/= C )

  proof
    wph
    cB
    cA
    cC
    wph
    cA
    cB
    eqnetrrd.1
    eqcomd
    eqnetrrd.2
    eqnetrd
end
