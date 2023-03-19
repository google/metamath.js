include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cpi.mm"
include "cneg.mm"
include "cpr.mm"
include "cc0.mm"
include "wceq.mm"
include "simpl3.mm"
include "simpl2.mm"
include "subcld.mm"
include "simpr2.mm"
include "necomd.mm"
include "subne0d.mm"
include "simpl1.mm"
include "simpr1.mm"
include "angneg.mm"
include "syl22anc.mm"
include "negsubdi2d.mm"
include "nnncan2d.mm"
include "eqtr4d.mm"
include "oveq12d.mm"
include "eqtr3d.mm"
include "simpr3.mm"
include "oveq1d.mm"
include "subneintr2d.mm"
include "ang180lem5.mm"
include "syl221anc.mm"
include "eqeltrd.mm"

theorem ang180
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume ang.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( ( A e. CC /\ B e. CC /\ C e. CC ) /\ ( A =/= B /\ B =/= C /\ A =/= C ) ) -> ( ( ( ( C - B ) F ( A - B ) ) + ( ( A - C ) F ( B - C ) ) ) + ( ( B - A ) F ( C - A ) ) ) e. { -u _pi , _pi } )

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
    cB
    wne
    #
    cB
    cC
    wne
    #
    cA
    cC
    wne
    #
    w3a
    #
    wa
    #
    cC
    cB
    cmin
    co
    #
    cA
    cB
    cmin
    co
    #
    cF
    co
    #
    cA
    cC
    cmin
    co
    #
    cB
    cC
    cmin
    co
    #
    cF
    co
    #
    caddc
    co
    #
    cB
    cA
    cmin
    co
    #
    cC
    cA
    cmin
    co
    #
    cF
    co
    #
    caddc
    co
    @16
    @17
    cmin
    co
    #
    @16
    cF
    co
    #
    @17
    @17
    @16
    cmin
    co
    #
    cF
    co
    #
    caddc
    co
    #
    @18
    caddc
    co
    #
    cpi
    cneg
    cpi
    cpr
    #
    @8
    @15
    @23
    @18
    caddc
    @8
    @11
    @20
    @14
    @22
    caddc
    @8
    @9
    cneg
    #
    @10
    cneg
    #
    cF
    co
    #
    @11
    @20
    @8
    @9
    cc
    wcel
    @9
    cc0
    wne
    @10
    cc
    wcel
    @10
    cc0
    wne
    @28
    @11
    wceq
    @8
    cC
    cB
    @0
    @1
    @2
    @7
    simpl3
    #
    @0
    @1
    @2
    @7
    simpl2
    #
    subcld
    @8
    cC
    cB
    @29
    @30
    @8
    cB
    cC
    @3
    @4
    @5
    @6
    simpr2
    #
    necomd
    subne0d
    @8
    cA
    cB
    @0
    @1
    @2
    @7
    simpl1
    #
    @30
    subcld
    @8
    cA
    cB
    @32
    @30
    @3
    @4
    @5
    @6
    simpr1
    #
    subne0d
    vx
    vy
    @9
    @10
    cF
    ang.1
    angneg
    syl22anc
    @8
    @26
    @19
    @27
    @16
    cF
    @8
    @26
    @13
    @19
    @8
    cC
    cB
    @29
    @30
    negsubdi2d
    @8
    cB
    cC
    cA
    @30
    @29
    @32
    nnncan2d
    eqtr4d
    @8
    cA
    cB
    @32
    @30
    negsubdi2d
    oveq12d
    eqtr3d
    @8
    @12
    cneg
    #
    @13
    cneg
    #
    cF
    co
    #
    @14
    @22
    @8
    @12
    cc
    wcel
    @12
    cc0
    wne
    @13
    cc
    wcel
    @13
    cc0
    wne
    @36
    @14
    wceq
    @8
    cA
    cC
    @32
    @29
    subcld
    @8
    cA
    cC
    @32
    @29
    @3
    @4
    @5
    @6
    simpr3
    #
    subne0d
    @8
    cB
    cC
    @30
    @29
    subcld
    @8
    cB
    cC
    @30
    @29
    @31
    subne0d
    vx
    vy
    @12
    @13
    cF
    ang.1
    angneg
    syl22anc
    @8
    @34
    @17
    @35
    @21
    cF
    @8
    cA
    cC
    @32
    @29
    negsubdi2d
    @8
    @35
    @9
    @21
    @8
    cB
    cC
    @30
    @29
    negsubdi2d
    @8
    cC
    cB
    cA
    @29
    @30
    @32
    nnncan2d
    eqtr4d
    oveq12d
    eqtr3d
    oveq12d
    oveq1d
    @8
    @16
    cc
    wcel
    @16
    cc0
    wne
    @17
    cc
    wcel
    @17
    cc0
    wne
    @16
    @17
    wne
    @24
    @25
    wcel
    @8
    cB
    cA
    @30
    @32
    subcld
    @8
    cB
    cA
    @30
    @32
    @8
    cA
    cB
    @33
    necomd
    subne0d
    @8
    cC
    cA
    @29
    @32
    subcld
    @8
    cC
    cA
    @29
    @32
    @8
    cA
    cC
    @37
    necomd
    subne0d
    @8
    cB
    cC
    cA
    @30
    @29
    @32
    @31
    subneintr2d
    vx
    vy
    @16
    @17
    cF
    ang.1
    ang180lem5
    syl221anc
    eqeltrd
end
