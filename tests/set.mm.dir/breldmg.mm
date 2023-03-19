include "wcel.mm"
include "wbr.mm"
include "cdm.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "breq2.mm"
include "spcegv.mm"
include "imp.mm"
include "eldmg.mm"
include "syl5ibr.mm"
include "3impib.mm"

theorem breldmg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. C /\ B e. D /\ A R B ) -> A e. dom R )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    cA
    cB
    cR
    wbr
    #
    cA
    cR
    cdm
    wcel
    #
    @1
    @2
    wa
    @3
    @0
    cA
    vx
    cv
    #
    cR
    wbr
    #
    vx
    wex
    #
    @1
    @2
    @6
    @5
    @2
    vx
    cB
    cD
    @4
    cB
    cA
    cR
    breq2
    spcegv
    imp
    vx
    cA
    cR
    cC
    eldmg
    syl5ibr
    3impib
end
