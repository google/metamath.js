include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "cmul.mm"
include "cdiv.mm"
include "cre.mm"
include "ccos.mm"
include "subcl.mm"
include "3adant2.mm"
include "adantr.mm"
include "3adant1.mm"
include "cc0.mm"
include "wb.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "bicomd.mm"
include "biimpa.mm"
include "adantrr.mm"
include "adantrl.mm"
include "lawcoslem1.mm"
include "wceq.mm"
include "nnncan2.mm"
include "fveq2d.mm"
include "syl6reqr.mm"
include "oveq1d.mm"
include "abscld.mm"
include "recnd.mm"
include "sqcld.mm"
include "addcomd.mm"
include "oveq1i.mm"
include "oveq12i.mm"
include "mulcomd.mm"
include "ci.mm"
include "clog.mm"
include "cim.mm"
include "ce.mm"
include "fveq2i.mm"
include "angvald.mm"
include "syl5eq.mm"
include "cr.mm"
include "divcld.mm"
include "divne0d.mm"
include "logcld.mm"
include "imcld.mm"
include "recosval.mm"
include "syl.mm"
include "eqtrd.mm"
include "efiarg.mm"
include "syl2anc.mm"
include "absne0d.mm"
include "redivd.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem lawcos
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
  assert |- ( ( ( A e. CC /\ B e. CC /\ C e. CC ) /\ ( A =/= C /\ B =/= C ) ) -> ( Z ^ 2 ) = ( ( ( X ^ 2 ) + ( Y ^ 2 ) ) - ( 2 x. ( ( X x. Y ) x. ( cos ` O ) ) ) ) )

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
    #
    cB
    cC
    wne
    #
    wa
    #
    wa
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
    cmin
    co
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @8
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @9
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    c2
    @13
    @15
    cmul
    co
    #
    @8
    @9
    cdiv
    co
    #
    cre
    cfv
    @19
    cabs
    cfv
    #
    cdiv
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
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
    @7
    @8
    @9
    @3
    @8
    cc
    wcel
    #
    @6
    @0
    @2
    @32
    @1
    cA
    cC
    subcl
    3adant2
    adantr
    #
    @3
    @9
    cc
    wcel
    #
    @6
    @1
    @2
    @34
    @0
    cB
    cC
    subcl
    3adant1
    adantr
    #
    @3
    @4
    @8
    cc0
    wne
    #
    @5
    @3
    @4
    @36
    @0
    @2
    @4
    @36
    wb
    @1
    @0
    @2
    wa
    #
    @36
    @4
    @37
    @8
    cc0
    cA
    cC
    cA
    cC
    subeq0
    necon3bid
    bicomd
    3adant2
    biimpa
    adantrr
    #
    @3
    @5
    @9
    cc0
    wne
    #
    @4
    @3
    @5
    @39
    @1
    @2
    @5
    @39
    wb
    @0
    @1
    @2
    wa
    #
    @39
    @5
    @40
    @9
    cc0
    cB
    cC
    cB
    cC
    subeq0
    necon3bid
    bicomd
    3adant1
    biimpa
    adantrl
    #
    lawcoslem1
    @3
    @24
    @12
    wceq
    @6
    @3
    cZ
    @11
    c2
    cexp
    @3
    @11
    cA
    cB
    cmin
    co
    #
    cabs
    cfv
    cZ
    @3
    @10
    @42
    cabs
    cA
    cB
    cC
    nnncan2
    fveq2d
    lawcos.4
    syl6reqr
    oveq1d
    adantr
    @7
    @27
    @17
    @31
    @23
    cmin
    @7
    @17
    @16
    @14
    caddc
    co
    @27
    @7
    @14
    @16
    @7
    @13
    @7
    @13
    @7
    @8
    @33
    abscld
    recnd
    #
    sqcld
    @7
    @15
    @7
    @15
    @7
    @9
    @35
    abscld
    recnd
    #
    sqcld
    addcomd
    @25
    @16
    @26
    @14
    caddc
    cX
    @15
    c2
    cexp
    lawcos.2
    oveq1i
    cY
    @13
    c2
    cexp
    lawcos.3
    oveq1i
    oveq12i
    syl6reqr
    @7
    @30
    @22
    c2
    cmul
    @7
    @28
    @18
    @29
    @21
    cmul
    @7
    @18
    @15
    @13
    cmul
    co
    @28
    @7
    @13
    @15
    @43
    @44
    mulcomd
    cX
    @15
    cY
    @13
    cmul
    lawcos.2
    lawcos.3
    oveq12i
    syl6reqr
    @7
    @29
    ci
    @19
    clog
    cfv
    #
    cim
    cfv
    #
    cmul
    co
    ce
    cfv
    #
    cre
    cfv
    #
    @19
    @20
    cdiv
    co
    #
    cre
    cfv
    @21
    @7
    @29
    @46
    ccos
    cfv
    #
    @48
    @7
    @29
    @9
    @8
    cF
    co
    #
    ccos
    cfv
    @50
    cO
    @51
    ccos
    lawcos.5
    fveq2i
    @7
    @51
    @46
    ccos
    @7
    vx
    vy
    cF
    @9
    @8
    lawcos.1
    @35
    @41
    @33
    @38
    angvald
    fveq2d
    syl5eq
    @7
    @46
    cr
    wcel
    @50
    @48
    wceq
    @7
    @45
    @7
    @19
    @7
    @8
    @9
    @33
    @35
    @41
    divcld
    #
    @7
    @8
    @9
    @33
    @35
    @38
    @41
    divne0d
    #
    logcld
    imcld
    @46
    recosval
    syl
    eqtrd
    @7
    @47
    @49
    cre
    @7
    @19
    cc
    wcel
    @19
    cc0
    wne
    @47
    @49
    wceq
    @52
    @53
    @19
    efiarg
    syl2anc
    fveq2d
    @7
    @20
    @19
    @7
    @19
    @52
    abscld
    @52
    @7
    @19
    @52
    @53
    absne0d
    redivd
    3eqtrd
    oveq12d
    oveq2d
    oveq12d
    3eqtr4d
end
