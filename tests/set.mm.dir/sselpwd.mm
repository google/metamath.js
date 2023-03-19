include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "cvv.mm"
include "wb.mm"
include "ssexd.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"

theorem sselpwd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  assume sselpwd.1: |- ( ph -> B e. V )
  assume sselpwd.2: |- ( ph -> A C_ B )


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
    sselpwd.2
    wph
    cA
    cvv
    wcel
    @0
    @1
    wb
    wph
    cA
    cB
    cV
    sselpwd.1
    sselpwd.2
    ssexd
    cA
    cB
    cvv
    elpwg
    syl
    mpbird
end
