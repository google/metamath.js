include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "wceq.mm"
include "crio.mm"
include "divval.mm"
include "wreu.mm"
include "receu.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem divcl
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( A / B ) e. CC )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cB
    cc0
    wne
    w3a
    #
    cA
    cB
    cdiv
    co
    cB
    vx
    cv
    cmul
    co
    cA
    wceq
    #
    vx
    cc
    crio
    #
    cc
    vx
    cA
    cB
    divval
    @0
    @1
    vx
    cc
    wreu
    @2
    cc
    wcel
    vx
    cA
    cB
    receu
    @1
    vx
    cc
    riotacl
    syl
    eqeltrd
end
