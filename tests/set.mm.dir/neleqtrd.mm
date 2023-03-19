include "wcel.mm"
include "eleq2d.mm"
include "mtbid.mm"

theorem neleqtrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume neleqtrd.1: |- ( ph -> -. C e. A )
  assume neleqtrd.2: |- ( ph -> A = B )


  assert |- ( ph -> -. C e. B )

  proof
    wph
    cC
    cA
    wcel
    cC
    cB
    wcel
    neleqtrd.1
    wph
    cA
    cB
    cC
    neleqtrd.2
    eleq2d
    mtbid
end
