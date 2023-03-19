include "ciin.mm"
include "cdm.mm"
include "wss.mm"
include "nfii1.mm"
include "nfdm.mm"
include "ssiinf.mm"
include "cv.mm"
include "wcel.mm"
include "iinss2.mm"
include "dmss.mm"
include "syl.mm"
include "mprgbir.mm"

theorem dmiin
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- dom |^|_ x e. A B C_ |^|_ x e. A dom B

  proof
    vx
    cA
    cB
    ciin
    #
    cdm
    #
    vx
    cA
    cB
    cdm
    #
    ciin
    wss
    @1
    @2
    wss
    #
    vx
    cA
    vx
    cA
    @2
    @1
    vx
    @0
    vx
    cA
    cB
    nfii1
    nfdm
    ssiinf
    vx
    cv
    cA
    wcel
    @0
    cB
    wss
    @3
    vx
    cA
    cB
    iinss2
    @0
    cB
    dmss
    syl
    mprgbir
end
