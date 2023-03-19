include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cpr.mm"
include "cexp.mm"
include "caddc.mm"
include "cmul.mm"
include "ccos.mm"
include "cfv.mm"
include "cmin.mm"
include "cc0.mm"
include "wceq.mm"
include "lawcos.mm"
include "3adant3.mm"
include "wo.mm"
include "elpri.mm"
include "fveq2.mm"
include "coshalfpi.mm"
include "syl6eq.mm"
include "cosneghalfpi.mm"
include "jaoi.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "oveq2d.mm"
include "cabs.mm"
include "subcl.mm"
include "3adant1.mm"
include "3ad2ant1.mm"
include "abscld.mm"
include "recnd.mm"
include "syl5eqel.mm"
include "3adant2.mm"
include "mulcld.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "2t0e0.mm"
include "sqcld.mm"
include "addcld.mm"
include "subid1d.mm"
include "3eqtrd.mm"

theorem pythag
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume lawcos.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )
  assume lawcos.2: |- X = ( abs ` ( B - C ) )
  assume lawcos.3: |- Y = ( abs ` ( A - C ) )
  assume lawcos.4: |- Z = ( abs ` ( A - B ) )
  assume lawcos.5: |- O = ( ( B - C ) F ( A - C ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( ( A e. CC /\ B e. CC /\ C e. CC ) /\ ( A =/= C /\ B =/= C ) /\ O e. { ( _pi / 2 ) , -u ( _pi / 2 ) } ) -> ( Z ^ 2 ) = ( ( X ^ 2 ) + ( Y ^ 2 ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    w3a
    #
    cA
    cC
    wne
    cB
    cC
    wne
    wa
    #
    cO
    cpi
    c2
    cdiv
    co
    #
    @5
    cneg
    #
    cpr
    wcel
    #
    w3a
    #
    cZ
    c2
    cexp
    co
    #
    cX
    c2
    cexp
    co
    #
    cY
    c2
    cexp
    co
    #
    caddc
    co
    #
    c2
    cX
    cY
    cmul
    co
    #
    cO
    ccos
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @12
    cc0
    cmin
    co
    @12
    @3
    @4
    @9
    @17
    wceq
    @7
    vx
    vy
    cA
    cB
    cC
    cF
    cO
    cX
    cY
    cZ
    lawcos.1
    lawcos.2
    lawcos.3
    lawcos.4
    lawcos.5
    lawcos
    3adant3
    @8
    @16
    cc0
    @12
    cmin
    @8
    @16
    c2
    cc0
    cmul
    co
    cc0
    @8
    @15
    cc0
    c2
    cmul
    @8
    @15
    @13
    cc0
    cmul
    co
    cc0
    @8
    @14
    cc0
    @13
    cmul
    @7
    @3
    @14
    cc0
    wceq
    #
    @4
    @7
    cO
    @5
    wceq
    #
    cO
    @6
    wceq
    #
    wo
    @18
    cO
    @5
    @6
    elpri
    @19
    @18
    @20
    @19
    @14
    @5
    ccos
    cfv
    cc0
    cO
    @5
    ccos
    fveq2
    coshalfpi
    syl6eq
    @20
    @14
    @6
    ccos
    cfv
    cc0
    cO
    @6
    ccos
    fveq2
    cosneghalfpi
    syl6eq
    jaoi
    syl
    3ad2ant3
    oveq2d
    @8
    @13
    @8
    cX
    cY
    @8
    cX
    cB
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    cc
    lawcos.2
    @8
    @22
    @8
    @21
    @3
    @4
    @21
    cc
    wcel
    #
    @7
    @1
    @2
    @23
    @0
    cB
    cC
    subcl
    3adant1
    3ad2ant1
    abscld
    recnd
    syl5eqel
    #
    @8
    cY
    cA
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    cc
    lawcos.3
    @8
    @26
    @8
    @25
    @3
    @4
    @25
    cc
    wcel
    #
    @7
    @0
    @2
    @27
    @1
    cA
    cC
    subcl
    3adant2
    3ad2ant1
    abscld
    recnd
    syl5eqel
    #
    mulcld
    mul01d
    eqtrd
    oveq2d
    2t0e0
    syl6eq
    oveq2d
    @8
    @12
    @8
    @10
    @11
    @8
    cX
    @24
    sqcld
    @8
    cY
    @28
    sqcld
    addcld
    subid1d
    3eqtrd
end
