include "wcel.mm"
include "wa.mm"
include "wor.mm"
include "wbr.mm"
include "wceq.mm"
include "w3o.mm"
include "cv.mm"
include "wi.mm"
include "breq1.mm"
include "eqeq1.mm"
include "breq2.mm"
include "3orbi123d.mm"
include "imbi2d.mm"
include "eqeq2.mm"
include "wpo.mm"
include "wral.mm"
include "df-so.mm"
include "rsp2.mm"
include "simplbiim.mm"
include "com12.mm"
include "vtocl2ga.mm"
include "impcom.mm"

theorem solin
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> ( B R C \/ B = C \/ C R B ) )

  proof
    cB
    cA
    wcel
    cC
    cA
    wcel
    wa
    cA
    cR
    wor
    #
    cB
    cC
    cR
    wbr
    #
    cB
    cC
    wceq
    #
    cC
    cB
    cR
    wbr
    #
    w3o
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @5
    @6
    wceq
    #
    @6
    @5
    cR
    wbr
    #
    w3o
    #
    wi
    @0
    cB
    @6
    cR
    wbr
    #
    cB
    @6
    wceq
    #
    @6
    cB
    cR
    wbr
    #
    w3o
    #
    wi
    @0
    @4
    wi
    vx
    vy
    cB
    cC
    cA
    cA
    @5
    cB
    wceq
    #
    @10
    @14
    @0
    @15
    @7
    @11
    @8
    @12
    @9
    @13
    @5
    cB
    @6
    cR
    breq1
    @5
    cB
    @6
    eqeq1
    @5
    cB
    @6
    cR
    breq2
    3orbi123d
    imbi2d
    @6
    cC
    wceq
    #
    @14
    @4
    @0
    @16
    @11
    @1
    @12
    @2
    @13
    @3
    @6
    cC
    cB
    cR
    breq2
    @6
    cC
    cB
    eqeq2
    @6
    cC
    cB
    cR
    breq1
    3orbi123d
    imbi2d
    @0
    @5
    cA
    wcel
    @6
    cA
    wcel
    wa
    #
    @10
    @0
    cA
    cR
    wpo
    @10
    vy
    cA
    wral
    vx
    cA
    wral
    @17
    @10
    wi
    vx
    vy
    cA
    cR
    df-so
    @10
    vx
    vy
    cA
    cA
    rsp2
    simplbiim
    com12
    vtocl2ga
    impcom
end
