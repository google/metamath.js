include "cuni.mm"
include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "wb.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbid.mm"
include "pwuniss.mm"
include "cvv.mm"
include "uniexg.mm"
include "3syl.mm"
include "mpbird.mm"

theorem elpwunicl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  assume elpwunicl.1: |- ( ph -> B e. V )
  assume elpwunicl.2: |- ( ph -> A e. ~P ~P B )


  assert |- ( ph -> U. A e. ~P B )

  proof
    wph
    cA
    cuni
    #
    cB
    cpw
    #
    wcel
    #
    @0
    cB
    wss
    #
    wph
    cA
    @1
    wss
    #
    @3
    wph
    cA
    @1
    cpw
    #
    wcel
    #
    @4
    elpwunicl.2
    wph
    @6
    @6
    @4
    wb
    elpwunicl.2
    cA
    @1
    @5
    elpwg
    syl
    mpbid
    cA
    cB
    pwuniss
    syl
    wph
    @6
    @0
    cvv
    wcel
    @2
    @3
    wb
    elpwunicl.2
    cA
    @5
    uniexg
    @0
    cB
    cvv
    elpwg
    3syl
    mpbird
end
