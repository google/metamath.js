include "com.mm"
include "con0.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "nnon.mm"
include "onfin.mm"
include "biimprcd.mm"
include "jcai.mm"
include "biimpa.mm"
include "impbii.mm"
include "elin.mm"
include "bitr4i.mm"
include "eqriv.mm"

theorem onfin2
  let vx: setvar x


  assert |- _om = ( On i^i Fin )

  proof
    vx
    com
    con0
    cfn
    cin
    #
    vx
    cv
    #
    com
    wcel
    #
    @1
    con0
    wcel
    #
    @1
    cfn
    wcel
    #
    wa
    #
    @1
    @0
    wcel
    @2
    @5
    @2
    @3
    @4
    @1
    nnon
    @3
    @4
    @2
    @1
    onfin
    #
    biimprcd
    jcai
    @3
    @4
    @2
    @6
    biimpa
    impbii
    @1
    con0
    cfn
    elin
    bitr4i
    eqriv
end
