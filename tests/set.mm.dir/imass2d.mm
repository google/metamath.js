include "wss.mm"
include "cima.mm"
include "imass2.mm"
include "syl.mm"

theorem imass2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume imass2d.1: |- ( ph -> A C_ B )


  assert |- ( ph -> ( C " A ) C_ ( C " B ) )

  proof
    wph
    cA
    cB
    wss
    cC
    cA
    cima
    cC
    cB
    cima
    wss
    imass2d.1
    cA
    cB
    cC
    imass2
    syl
end
