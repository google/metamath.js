include "eqcomd.mm"
include "neleqtrd.mm"

theorem neleqtrrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume neleqtrrd.1: |- ( ph -> -. C e. B )
  assume neleqtrrd.2: |- ( ph -> A = B )


  assert |- ( ph -> -. C e. A )

  proof
    wph
    cB
    cA
    cC
    neleqtrrd.1
    wph
    cA
    cB
    neleqtrrd.2
    eqcomd
    neleqtrd
end
