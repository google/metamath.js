include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "wb.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"

theorem elpwd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  assume elpwd.1: |- ( ph -> A e. V )
  assume elpwd.2: |- ( ph -> A C_ B )


  assert |- ( ph -> A e. ~P B )

  proof
    wph
    cA
    cB
    cpw
    wcel
    #
    cA
    cB
    wss
    #
    elpwd.2
    wph
    cA
    cV
    wcel
    @0
    @1
    wb
    elpwd.1
    cA
    cB
    cV
    elpwg
    syl
    mpbird
end
