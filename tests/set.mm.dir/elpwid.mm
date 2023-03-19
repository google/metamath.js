include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "elpwi.mm"
include "syl.mm"

theorem elpwid
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume elpwid.1: |- ( ph -> A e. ~P B )


  assert |- ( ph -> A C_ B )

  proof
    wph
    cA
    cB
    cpw
    wcel
    cA
    cB
    wss
    elpwid.1
    cA
    cB
    elpwi
    syl
end
