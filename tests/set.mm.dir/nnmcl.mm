include "com.mm"
include "wcel.mm"
include "comu.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "c0.mm"
include "csuc.mm"
include "nnm0.mm"
include "peano1.mm"
include "syl6eqel.mm"
include "wa.mm"
include "coa.mm"
include "nnacl.mm"
include "expcom.mm"
include "adantr.mm"
include "nnmsuc.mm"
include "sylibrd.mm"
include "finds2.mm"
include "vtoclga.mm"
include "impcom.mm"

theorem nnmcl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. _om /\ B e. _om ) -> ( A .o B ) e. _om )

  proof
    cB
    com
    wcel
    cA
    com
    wcel
    #
    cA
    cB
    comu
    co
    #
    com
    wcel
    #
    @0
    cA
    vx
    cv
    #
    comu
    co
    #
    com
    wcel
    #
    wi
    @0
    @2
    wi
    vx
    cB
    com
    @3
    cB
    wceq
    #
    @5
    @2
    @0
    @6
    @4
    @1
    com
    @3
    cB
    cA
    comu
    oveq2
    eleq1d
    imbi2d
    @5
    cA
    c0
    comu
    co
    #
    com
    wcel
    cA
    vy
    cv
    #
    comu
    co
    #
    com
    wcel
    #
    cA
    @8
    csuc
    #
    comu
    co
    #
    com
    wcel
    #
    @0
    vx
    vy
    @3
    c0
    wceq
    @4
    @7
    com
    @3
    c0
    cA
    comu
    oveq2
    eleq1d
    @3
    @8
    wceq
    @4
    @9
    com
    @3
    @8
    cA
    comu
    oveq2
    eleq1d
    @3
    @11
    wceq
    @4
    @12
    com
    @3
    @11
    cA
    comu
    oveq2
    eleq1d
    @0
    @7
    c0
    com
    cA
    nnm0
    peano1
    syl6eqel
    @0
    @8
    com
    wcel
    #
    @10
    @13
    wi
    @0
    @14
    wa
    #
    @10
    @9
    cA
    coa
    co
    #
    com
    wcel
    #
    @13
    @0
    @10
    @17
    wi
    @14
    @10
    @0
    @17
    @9
    cA
    nnacl
    expcom
    adantr
    @15
    @12
    @16
    com
    cA
    @8
    nnmsuc
    eleq1d
    sylibrd
    expcom
    finds2
    vtoclga
    impcom
end
