include "com.mm"
include "wcel.mm"
include "coe.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "c0.mm"
include "csuc.mm"
include "c1o.mm"
include "con0.mm"
include "nnon.mm"
include "oe0.mm"
include "syl.mm"
include "df-1o.mm"
include "peano1.mm"
include "peano2.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "wa.mm"
include "comu.mm"
include "nnmcl.mm"
include "expcom.mm"
include "adantr.mm"
include "nnesuc.mm"
include "sylibrd.mm"
include "finds2.mm"
include "vtoclga.mm"
include "impcom.mm"

theorem nnecl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. _om /\ B e. _om ) -> ( A ^o B ) e. _om )

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
    coe
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
    coe
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
    coe
    oveq2
    eleq1d
    imbi2d
    @5
    cA
    c0
    coe
    co
    #
    com
    wcel
    cA
    vy
    cv
    #
    coe
    co
    #
    com
    wcel
    #
    cA
    @8
    csuc
    #
    coe
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
    coe
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
    coe
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
    coe
    oveq2
    eleq1d
    @0
    @7
    c1o
    com
    @0
    cA
    con0
    wcel
    @7
    c1o
    wceq
    cA
    nnon
    cA
    oe0
    syl
    c1o
    c0
    csuc
    #
    com
    df-1o
    c0
    com
    wcel
    @14
    com
    wcel
    peano1
    c0
    peano2
    ax-mp
    eqeltri
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
    @15
    wa
    #
    @10
    @9
    cA
    comu
    co
    #
    com
    wcel
    #
    @13
    @0
    @10
    @18
    wi
    @15
    @10
    @0
    @18
    @9
    cA
    nnmcl
    expcom
    adantr
    @16
    @12
    @17
    com
    cA
    @8
    nnesuc
    eleq1d
    sylibrd
    expcom
    finds2
    vtoclga
    impcom
end
