include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cv.mm"
include "caddc.mm"
include "wceq.mm"
include "crio.mm"
include "subval.mm"
include "wreu.mm"
include "negeu.mm"
include "ancoms.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem subcl
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A - B ) e. CC )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    cmin
    co
    cB
    vx
    cv
    caddc
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
    subval
    @2
    @3
    vx
    cc
    wreu
    #
    @4
    cc
    wcel
    @1
    @0
    @5
    vx
    cB
    cA
    negeu
    ancoms
    @3
    vx
    cc
    riotacl
    syl
    eqeltrd
end
