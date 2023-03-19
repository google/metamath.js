include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "syl.mm"

theorem ne0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ne0d.1: |- ( ph -> B e. A )


  assert |- ( ph -> A =/= (/) )

  proof
    wph
    cB
    cA
    wcel
    cA
    c0
    wne
    ne0d.1
    cA
    cB
    ne0i
    syl
end
