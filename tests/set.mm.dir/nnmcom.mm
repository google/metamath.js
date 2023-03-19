include "com.mm"
include "wcel.mm"
include "comu.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "oveq1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "c0.mm"
include "csuc.mm"
include "nnm0r.mm"
include "nnm0.mm"
include "eqtr4d.mm"
include "wa.mm"
include "coa.mm"
include "nnmsucr.mm"
include "nnmsuc.mm"
include "ancoms.mm"
include "syl5ibr.mm"
include "ex.mm"
include "finds2.mm"
include "vtoclga.mm"
include "imp.mm"

theorem nnmcom
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C


  assert |- ( ( A e. _om /\ B e. _om ) -> ( A .o B ) = ( B .o A ) )

  proof
    cA
    com
    wcel
    cB
    com
    wcel
    #
    cA
    cB
    comu
    co
    #
    cB
    cA
    comu
    co
    #
    wceq
    #
    @0
    vx
    cv
    #
    cB
    comu
    co
    #
    cB
    @4
    comu
    co
    #
    wceq
    #
    wi
    @0
    @3
    wi
    vx
    cA
    com
    @4
    cA
    wceq
    #
    @7
    @3
    @0
    @8
    @5
    @1
    @6
    @2
    @4
    cA
    cB
    comu
    oveq1
    @4
    cA
    cB
    comu
    oveq2
    eqeq12d
    imbi2d
    @7
    c0
    cB
    comu
    co
    #
    cB
    c0
    comu
    co
    #
    wceq
    vy
    cv
    #
    cB
    comu
    co
    #
    cB
    @11
    comu
    co
    #
    wceq
    #
    @11
    csuc
    #
    cB
    comu
    co
    #
    cB
    @15
    comu
    co
    #
    wceq
    #
    @0
    vx
    vy
    @4
    c0
    wceq
    @5
    @9
    @6
    @10
    @4
    c0
    cB
    comu
    oveq1
    @4
    c0
    cB
    comu
    oveq2
    eqeq12d
    @4
    @11
    wceq
    @5
    @12
    @6
    @13
    @4
    @11
    cB
    comu
    oveq1
    @4
    @11
    cB
    comu
    oveq2
    eqeq12d
    @4
    @15
    wceq
    @5
    @16
    @6
    @17
    @4
    @15
    cB
    comu
    oveq1
    @4
    @15
    cB
    comu
    oveq2
    eqeq12d
    @0
    @9
    c0
    @10
    cB
    nnm0r
    cB
    nnm0
    eqtr4d
    @11
    com
    wcel
    #
    @0
    @14
    @18
    wi
    @14
    @18
    @19
    @0
    wa
    #
    @12
    cB
    coa
    co
    #
    @13
    cB
    coa
    co
    #
    wceq
    @12
    @13
    cB
    coa
    oveq1
    @20
    @16
    @21
    @17
    @22
    @11
    cB
    nnmsucr
    @0
    @19
    @17
    @22
    wceq
    cB
    @11
    nnmsuc
    ancoms
    eqeq12d
    syl5ibr
    ex
    finds2
    vtoclga
    imp
end
