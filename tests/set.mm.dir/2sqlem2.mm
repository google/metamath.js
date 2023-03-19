include "wcel.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "cabs.mm"
include "cfv.mm"
include "cgz.mm"
include "2sqlem1.mm"
include "cre.mm"
include "cim.mm"
include "cc.mm"
include "elgz.mm"
include "simp2bi.mm"
include "simp3bi.mm"
include "gzcn.mm"
include "absvalsq2d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "oveq2d.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "gzreim.mm"
include "zcn.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcl.mm"
include "syl2an.mm"
include "cr.mm"
include "zre.mm"
include "crre.mm"
include "crim.mm"
include "oveq12d.mm"
include "eqtr2d.mm"
include "fveq2.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "sylibr.mm"
include "eleq1.mm"
include "rexlimivv.mm"
include "impbii.mm"

theorem 2sqlem2
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vz: setvar z
  let vm: setvar m
  let cC: class C
  let vu: setvar u
  let vv: setvar v
  let wph: wff ph
  let cB: class B
  let cM: class M
  let cD: class D
  let cE: class E
  let cN: class N
  let cY: class Y
  let cF: class F
  let cP: class P
  assume 2sq.1: |- S = ran ( w e. Z[i] |-> ( ( abs ` w ) ^ 2 ) )

  disjoint w x
  disjoint w y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint S x
  disjoint S y
  disjoint a b
  disjoint a n
  disjoint a p
  disjoint a q
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b n
  disjoint b p
  disjoint b q
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint n p
  disjoint n q
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p q
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint a m
  disjoint A a
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint A z
  disjoint C x
  disjoint p u
  disjoint p v
  disjoint p ph
  disjoint q u
  disjoint q v
  disjoint ph q
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint B a
  disjoint b m
  disjoint B b
  disjoint m p
  disjoint B m
  disjoint B p
  disjoint B x
  disjoint B y
  disjoint a u
  disjoint a v
  disjoint M a
  disjoint b u
  disjoint b v
  disjoint M b
  disjoint M p
  disjoint u z
  disjoint M u
  disjoint v z
  disjoint M v
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint S a
  disjoint S b
  disjoint m n
  disjoint m q
  disjoint m u
  disjoint m v
  disjoint S m
  disjoint n u
  disjoint n v
  disjoint S n
  disjoint S p
  disjoint S q
  disjoint S u
  disjoint S v
  disjoint S z
  disjoint D x
  disjoint E a
  disjoint E p
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint N p
  disjoint N q
  disjoint N u
  disjoint N v
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Y a
  disjoint Y b
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint Y y
  disjoint F a
  disjoint F p
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint P n
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint P y
  assert |- ( A e. S <-> E. x e. ZZ E. y e. ZZ A = ( ( x ^ 2 ) + ( y ^ 2 ) ) )

  proof
    cA
    cS
    wcel
    #
    cA
    vx
    cv
    #
    c2
    cexp
    co
    #
    vy
    cv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    @0
    cA
    vz
    cv
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    #
    vz
    cgz
    wrex
    @7
    vz
    vw
    cA
    cS
    2sq.1
    2sqlem1
    @11
    @7
    vz
    cgz
    @8
    cgz
    wcel
    #
    @7
    @11
    @10
    @5
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    @12
    @8
    cre
    cfv
    #
    cz
    wcel
    #
    @8
    cim
    cfv
    #
    cz
    wcel
    #
    @10
    @15
    c2
    cexp
    co
    #
    @17
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    @14
    @12
    @8
    cc
    wcel
    #
    @16
    @18
    @8
    elgz
    #
    simp2bi
    @12
    @23
    @16
    @18
    @24
    simp3bi
    @12
    @8
    @8
    gzcn
    absvalsq2d
    @13
    @22
    @10
    @19
    @4
    caddc
    co
    #
    wceq
    vx
    vy
    @15
    @17
    cz
    cz
    @1
    @15
    wceq
    #
    @5
    @25
    @10
    @26
    @2
    @19
    @4
    caddc
    @1
    @15
    c2
    cexp
    oveq1
    oveq1d
    eqeq2d
    @3
    @17
    wceq
    #
    @25
    @21
    @10
    @27
    @4
    @20
    @19
    caddc
    @3
    @17
    c2
    cexp
    oveq1
    oveq2d
    eqeq2d
    rspc2ev
    syl3anc
    @11
    @6
    @13
    vx
    vy
    cz
    cz
    cA
    @10
    @5
    eqeq1
    2rexbidv
    syl5ibrcom
    rexlimiv
    sylbi
    @6
    @0
    vx
    vy
    cz
    cz
    @1
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    wa
    #
    @0
    @6
    @5
    cS
    wcel
    #
    @30
    @5
    @10
    wceq
    #
    vz
    cgz
    wrex
    #
    @31
    @30
    @1
    ci
    @3
    cmul
    co
    #
    caddc
    co
    #
    cgz
    wcel
    @5
    @35
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    #
    @33
    @1
    @3
    gzreim
    @30
    @37
    @35
    cre
    cfv
    #
    c2
    cexp
    co
    #
    @35
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    @5
    @30
    @35
    @28
    @1
    cc
    wcel
    @34
    cc
    wcel
    #
    @35
    cc
    wcel
    @29
    @1
    zcn
    @29
    ci
    cc
    wcel
    @3
    cc
    wcel
    @43
    ax-icn
    @3
    zcn
    ci
    @3
    mulcl
    sylancr
    @1
    @34
    addcl
    syl2an
    absvalsq2d
    @30
    @40
    @2
    @42
    @4
    caddc
    @30
    @39
    @1
    c2
    cexp
    @28
    @1
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @39
    @1
    wceq
    @29
    @1
    zre
    #
    @3
    zre
    #
    @1
    @3
    crre
    syl2an
    oveq1d
    @30
    @41
    @3
    c2
    cexp
    @28
    @44
    @45
    @41
    @3
    wceq
    @29
    @46
    @47
    @1
    @3
    crim
    syl2an
    oveq1d
    oveq12d
    eqtr2d
    @32
    @38
    vz
    @35
    cgz
    @8
    @35
    wceq
    #
    @10
    @37
    @5
    @48
    @9
    @36
    c2
    cexp
    @8
    @35
    cabs
    fveq2
    oveq1d
    eqeq2d
    rspcev
    syl2anc
    vz
    vw
    @5
    cS
    2sq.1
    2sqlem1
    sylibr
    cA
    @5
    cS
    eleq1
    syl5ibrcom
    rexlimivv
    impbii
end
