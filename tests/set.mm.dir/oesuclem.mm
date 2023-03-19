include "wcel.mm"
include "csuc.mm"
include "coe.mm"
include "co.mm"
include "comu.mm"
include "wceq.mm"
include "c0.mm"
include "wa.mm"
include "oveq1.mm"
include "word.mm"
include "wlim.mm"
include "limord.mm"
include "ax-mp.mm"
include "ordelord.mm"
include "mpan.mm"
include "0elsuc.mm"
include "syl.mm"
include "wb.mm"
include "limsuc.mm"
include "con0.mm"
include "ordelon.mm"
include "oe0m1.mm"
include "sylbi.mm"
include "mpbid.mm"
include "sylan9eqr.mm"
include "id.mm"
include "oveq12d.mm"
include "oveq2.mm"
include "c1o.mm"
include "oe0m0.mm"
include "1on.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "adantl.mm"
include "biimpa.mm"
include "0elon.mm"
include "adantll.mm"
include "oe0lem.mm"
include "mpancom.mm"
include "om0.mm"
include "eqtr4d.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt.mm"
include "crdg.mm"
include "cfv.mm"
include "ad2antlr.mm"
include "oevn0.mm"
include "sylanl2.mm"
include "ovex.mm"
include "eqid.mm"
include "fvmpt.mm"
include "fveq2d.mm"
include "syl5eqr.mm"
include "3eqtr4d.mm"

theorem oesuclem
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cX: class X
  assume oesuclem.1: |- Lim X
  assume oesuclem.2: |- ( B e. X -> ( rec ( ( x e. _V |-> ( x .o A ) ) , 1o ) ` suc B ) = ( ( x e. _V |-> ( x .o A ) ) ` ( rec ( ( x e. _V |-> ( x .o A ) ) , 1o ) ` B ) ) )

  disjoint A x
  disjoint B x
  assert |- ( ( A e. On /\ B e. X ) -> ( A ^o suc B ) = ( ( A ^o B ) .o A ) )

  proof
    cB
    cX
    wcel
    #
    cA
    cB
    csuc
    #
    coe
    co
    #
    cA
    cB
    coe
    co
    #
    cA
    comu
    co
    #
    wceq
    cA
    @0
    cA
    c0
    wceq
    #
    wa
    @2
    c0
    @4
    @5
    @0
    @2
    c0
    @1
    coe
    co
    #
    c0
    cA
    c0
    @1
    coe
    oveq1
    @0
    c0
    @1
    wcel
    #
    @6
    c0
    wceq
    #
    @0
    cB
    word
    #
    @7
    cX
    word
    #
    @0
    @9
    cX
    wlim
    #
    @10
    oesuclem.1
    cX
    limord
    ax-mp
    #
    cX
    cB
    ordelord
    mpan
    cB
    0elsuc
    syl
    @0
    @1
    cX
    wcel
    #
    @7
    @8
    wb
    #
    @11
    @0
    @13
    wb
    oesuclem.1
    cX
    cB
    limsuc
    ax-mp
    #
    @13
    @1
    con0
    wcel
    #
    @14
    @10
    @13
    @16
    @12
    cX
    @1
    ordelon
    mpan
    #
    @1
    oe0m1
    syl
    sylbi
    mpbid
    sylan9eqr
    @5
    @0
    @4
    c0
    cB
    coe
    co
    #
    c0
    comu
    co
    #
    c0
    @5
    @3
    @18
    cA
    c0
    comu
    cA
    c0
    cB
    coe
    oveq1
    @5
    id
    oveq12d
    @0
    @18
    con0
    wcel
    #
    @19
    c0
    wceq
    cB
    con0
    wcel
    #
    @0
    @20
    @10
    @0
    @21
    @12
    cX
    cB
    ordelon
    mpan
    #
    @0
    @20
    cB
    cB
    c0
    wceq
    #
    @20
    @0
    @23
    @18
    c0
    c0
    coe
    co
    #
    con0
    cB
    c0
    c0
    coe
    oveq2
    @24
    c1o
    con0
    oe0m0
    1on
    eqeltri
    syl6eqel
    adantl
    @0
    c0
    cB
    wcel
    #
    @20
    @21
    @0
    @25
    wa
    @18
    c0
    con0
    @0
    @25
    @18
    c0
    wceq
    #
    @0
    @21
    @25
    @26
    wb
    @22
    cB
    oe0m1
    syl
    biimpa
    0elon
    syl6eqel
    adantll
    oe0lem
    mpancom
    @18
    om0
    syl
    sylan9eqr
    eqtr4d
    cA
    con0
    wcel
    #
    @0
    wa
    c0
    cA
    wcel
    #
    wa
    #
    @1
    vx
    cvv
    vx
    cv
    #
    cA
    comu
    co
    #
    cmpt
    #
    c1o
    crdg
    #
    cfv
    #
    cB
    @33
    cfv
    #
    @32
    cfv
    #
    @2
    @4
    @0
    @34
    @36
    wceq
    @27
    @28
    oesuclem.2
    ad2antlr
    @0
    @27
    @16
    @28
    @2
    @34
    wceq
    @0
    @13
    @16
    @15
    @17
    sylbi
    vx
    cA
    @1
    oevn0
    sylanl2
    @29
    @4
    @3
    @32
    cfv
    #
    @36
    @3
    cvv
    wcel
    @37
    @4
    wceq
    cA
    cB
    coe
    ovex
    vx
    @3
    @31
    @4
    cvv
    @32
    @30
    @3
    cA
    comu
    oveq1
    @32
    eqid
    @3
    cA
    comu
    ovex
    fvmpt
    ax-mp
    @29
    @3
    @35
    @32
    @0
    @27
    @21
    @28
    @3
    @35
    wceq
    @22
    vx
    cA
    cB
    oevn0
    sylanl2
    fveq2d
    syl5eqr
    3eqtr4d
    oe0lem
end
