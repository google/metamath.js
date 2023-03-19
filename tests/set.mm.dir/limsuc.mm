include "wlim.mm"
include "wcel.mm"
include "csuc.mm"
include "word.mm"
include "c0.mm"
include "cv.mm"
include "wral.mm"
include "w3a.mm"
include "wi.mm"
include "dflim4.mm"
include "wceq.mm"
include "suceq.mm"
include "eleq1d.mm"
include "rspccv.mm"
include "3ad2ant3.mm"
include "sylbi.mm"
include "wtr.mm"
include "limord.mm"
include "ordtr.mm"
include "trsuc.mm"
include "ex.mm"
include "3syl.mm"
include "impbid.mm"

theorem limsuc
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( Lim A -> ( B e. A <-> suc B e. A ) )

  proof
    cA
    wlim
    #
    cB
    cA
    wcel
    #
    cB
    csuc
    #
    cA
    wcel
    #
    @0
    cA
    word
    #
    c0
    cA
    wcel
    #
    vx
    cv
    #
    csuc
    #
    cA
    wcel
    #
    vx
    cA
    wral
    #
    w3a
    @1
    @3
    wi
    #
    vx
    cA
    dflim4
    @9
    @4
    @10
    @5
    @8
    @3
    vx
    cB
    cA
    @6
    cB
    wceq
    @7
    @2
    cA
    @6
    cB
    suceq
    eleq1d
    rspccv
    3ad2ant3
    sylbi
    @0
    @4
    cA
    wtr
    #
    @3
    @1
    wi
    cA
    limord
    cA
    ordtr
    @11
    @3
    @1
    cA
    cB
    trsuc
    ex
    3syl
    impbid
end
