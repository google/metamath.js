include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "simp1l.mm"
include "simp21.mm"
include "simp1r.mm"
include "subcld.mm"
include "simp23.mm"
include "subne0d.mm"
include "angneg.mm"
include "syl22anc.mm"
include "negsubdi2d.mm"
include "oveq2d.mm"
include "c1.mm"
include "cdiv.mm"
include "clog.mm"
include "cim.mm"
include "1cnd.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "divcld.mm"
include "necomd.mm"
include "divne1d.mm"
include "angvald.mm"
include "div1d.mm"
include "fveq2d.mm"
include "wn.mm"
include "absdivd.mm"
include "simp3.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "abscld.mm"
include "recnd.mm"
include "absne0d.mm"
include "dividd.mm"
include "3eqtrd.mm"
include "neneqd.mm"
include "isosctrlem2.mm"
include "syl3anc.mm"
include "negcld.mm"
include "simp22.mm"
include "divne0d.mm"
include "negne0d.mm"
include "eqtr4d.mm"
include "cmul.mm"
include "mulid1d.mm"
include "subdid.mm"
include "divcan2d.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "angcan.mm"
include "syl222anc.mm"
include "eqtr3d.mm"
include "mulneg2d.mm"
include "negeqd.mm"
include "3eqtr4d.mm"
include "3eqtr3d.mm"

theorem isosctrlem3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cC: class C
  assume isosctrlem3.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ( ( A e. CC /\ B e. CC ) /\ ( A =/= 0 /\ B =/= 0 /\ A =/= B ) /\ ( abs ` A ) = ( abs ` B ) ) -> ( -u A F ( B - A ) ) = ( ( A - B ) F -u B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cc0
    wne
    #
    cB
    cc0
    wne
    #
    cA
    cB
    wne
    #
    w3a
    #
    cA
    cabs
    cfv
    #
    cB
    cabs
    cfv
    #
    wceq
    #
    w3a
    #
    cA
    cneg
    #
    cA
    cB
    cmin
    co
    #
    cneg
    #
    cF
    co
    #
    cA
    @12
    cF
    co
    #
    @11
    cB
    cA
    cmin
    co
    #
    cF
    co
    @12
    cB
    cneg
    #
    cF
    co
    #
    @10
    @0
    @3
    @12
    cc
    wcel
    @12
    cc0
    wne
    @14
    @15
    wceq
    @0
    @1
    @6
    @9
    simp1l
    #
    @2
    @3
    @4
    @5
    @9
    simp21
    #
    @10
    cA
    cB
    @19
    @0
    @1
    @6
    @9
    simp1r
    #
    subcld
    @10
    cA
    cB
    @19
    @21
    @2
    @3
    @4
    @5
    @9
    simp23
    #
    subne0d
    vx
    vy
    cA
    @12
    cF
    isosctrlem3.1
    angneg
    syl22anc
    @10
    @13
    @16
    @11
    cF
    @10
    cA
    cB
    @19
    @21
    negsubdi2d
    oveq2d
    @10
    c1
    c1
    cB
    cA
    cdiv
    co
    #
    cmin
    co
    #
    cF
    co
    #
    @24
    @23
    cneg
    #
    cF
    co
    #
    @15
    @18
    @10
    @25
    @24
    c1
    cdiv
    co
    #
    clog
    cfv
    #
    cim
    cfv
    @24
    clog
    cfv
    #
    cim
    cfv
    #
    @27
    @10
    vx
    vy
    cF
    c1
    @24
    isosctrlem3.1
    @10
    1cnd
    #
    c1
    cc0
    wne
    #
    @10
    ax-1ne0
    a1i
    #
    @10
    c1
    @23
    @32
    @10
    cB
    cA
    @21
    @19
    @20
    divcld
    #
    subcld
    #
    @10
    c1
    @23
    @32
    @35
    @10
    @23
    c1
    @10
    cB
    cA
    @21
    @19
    @20
    @10
    cA
    cB
    @22
    necomd
    divne1d
    necomd
    #
    subne0d
    #
    angvald
    @10
    @29
    @30
    cim
    @10
    @28
    @24
    clog
    @10
    @24
    @36
    div1d
    fveq2d
    fveq2d
    @10
    @31
    @26
    @24
    cdiv
    co
    clog
    cfv
    cim
    cfv
    #
    @27
    @10
    @23
    cc
    wcel
    @23
    cabs
    cfv
    #
    c1
    wceq
    c1
    @23
    wceq
    wn
    @31
    @39
    wceq
    @35
    @10
    @40
    @8
    @7
    cdiv
    co
    @7
    @7
    cdiv
    co
    c1
    @10
    cB
    cA
    @21
    @19
    @20
    absdivd
    @10
    @8
    @7
    @7
    cdiv
    @10
    @7
    @8
    @2
    @6
    @9
    simp3
    eqcomd
    oveq1d
    @10
    @7
    @10
    @7
    @10
    cA
    @19
    abscld
    recnd
    @10
    cA
    @19
    @20
    absne0d
    dividd
    3eqtrd
    @10
    c1
    @23
    @37
    neneqd
    @23
    isosctrlem2
    syl3anc
    @10
    vx
    vy
    cF
    @24
    @26
    isosctrlem3.1
    @36
    @38
    @10
    @23
    @35
    negcld
    #
    @10
    @23
    @35
    @10
    cB
    cA
    @21
    @19
    @2
    @3
    @4
    @5
    @9
    simp22
    @20
    divne0d
    negne0d
    #
    angvald
    eqtr4d
    3eqtrd
    @10
    cA
    c1
    cmul
    co
    #
    cA
    @24
    cmul
    co
    #
    cF
    co
    #
    @15
    @25
    @10
    @43
    cA
    @44
    @12
    cF
    @10
    cA
    @19
    mulid1d
    #
    @10
    @44
    @43
    cA
    @23
    cmul
    co
    #
    cmin
    co
    @12
    @10
    cA
    c1
    @23
    @19
    @32
    @35
    subdid
    @10
    @43
    cA
    @47
    cB
    cmin
    @46
    @10
    cB
    cA
    @21
    @19
    @20
    divcan2d
    #
    oveq12d
    eqtrd
    #
    oveq12d
    @10
    c1
    cc
    wcel
    @33
    @24
    cc
    wcel
    #
    @24
    cc0
    wne
    #
    @0
    @3
    @45
    @25
    wceq
    @32
    @34
    @36
    @38
    @19
    @20
    vx
    vy
    c1
    @24
    cA
    cF
    isosctrlem3.1
    angcan
    syl222anc
    eqtr3d
    @10
    @44
    cA
    @26
    cmul
    co
    #
    cF
    co
    #
    @18
    @27
    @10
    @44
    @12
    @52
    @17
    cF
    @49
    @10
    @52
    @47
    cneg
    @17
    @10
    cA
    @23
    @19
    @35
    mulneg2d
    @10
    @47
    cB
    @48
    negeqd
    eqtrd
    oveq12d
    @10
    @50
    @51
    @26
    cc
    wcel
    @26
    cc0
    wne
    @0
    @3
    @53
    @27
    wceq
    @36
    @38
    @41
    @42
    @19
    @20
    vx
    vy
    @24
    @26
    cA
    cF
    isosctrlem3.1
    angcan
    syl222anc
    eqtr3d
    3eqtr4d
    3eqtr3d
end
