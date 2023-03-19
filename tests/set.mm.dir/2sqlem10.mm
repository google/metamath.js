include "wcel.mm"
include "cn.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "elfz1end.mm"
include "biimpi.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "raleqdv.mm"
include "elfz1eq.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "cgz.mm"
include "wrex.mm"
include "cz.mm"
include "1z.mm"
include "zgz.mm"
include "ax-mp.mm"
include "sq1.mm"
include "eqcomi.mm"
include "fveq2.mm"
include "abs1.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "2sqlem1.mm"
include "mpbir.mm"
include "syl6eqel.mm"
include "a1d.mm"
include "ralrimivw.mm"
include "rgen.mm"
include "csn.mm"
include "wa.mm"
include "cmin.mm"
include "simplr.mm"
include "cc.mm"
include "nncn.mm"
include "ad2antrr.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "mpbird.mm"
include "simprr.mm"
include "peano2nn.mm"
include "simprl.mm"
include "2sqlem9.mm"
include "expr.mm"
include "ralrimiva.mm"
include "ex.mm"
include "breq2.mm"
include "imbi1d.mm"
include "cbvralv.mm"
include "syl6ibr.mm"
include "ovex.mm"
include "breq1.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "ralsn.mm"
include "ancld.mm"
include "cun.mm"
include "cuz.mm"
include "elnnuz.mm"
include "fzsuc.mm"
include "sylbi.mm"
include "ralunb.mm"
include "syl6bb.mm"
include "sylibrd.mm"
include "nnind.mm"
include "rspcv.mm"
include "sylc.mm"
include "syl5.mm"
include "3imp.mm"

theorem 2sqlem10
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cS: class S
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vm: setvar m
  let cC: class C
  let vu: setvar u
  let vv: setvar v
  let wph: wff ph
  let cM: class M
  let cD: class D
  let cE: class E
  let cN: class N
  let cF: class F
  let cP: class P
  assume 2sq.1: |- S = ran ( w e. Z[i] |-> ( ( abs ` w ) ^ 2 ) )
  assume 2sqlem7.2: |- Y = { z | E. x e. ZZ E. y e. ZZ ( ( x gcd y ) = 1 /\ z = ( ( x ^ 2 ) + ( y ^ 2 ) ) ) }

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint Y x
  disjoint Y y
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
  disjoint a m
  disjoint A a
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
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
  assert |- ( ( A e. Y /\ B e. NN /\ B || A ) -> B e. S )

  proof
    cA
    cY
    wcel
    #
    cB
    cn
    wcel
    #
    cB
    cA
    cdvds
    wbr
    #
    cB
    cS
    wcel
    #
    @1
    cB
    va
    cv
    #
    cdvds
    wbr
    #
    @3
    wi
    #
    va
    cY
    wral
    #
    @0
    @2
    @3
    wi
    #
    @1
    cB
    c1
    cB
    cfz
    co
    #
    wcel
    #
    vb
    cv
    #
    @4
    cdvds
    wbr
    #
    @11
    cS
    wcel
    #
    wi
    #
    va
    cY
    wral
    #
    vb
    @9
    wral
    #
    @7
    @1
    @10
    cB
    elfz1end
    biimpi
    @15
    vb
    c1
    vm
    cv
    #
    cfz
    co
    #
    wral
    @15
    vb
    c1
    c1
    cfz
    co
    #
    wral
    @15
    vb
    c1
    vn
    cv
    #
    cfz
    co
    #
    wral
    #
    @15
    vb
    c1
    @20
    c1
    caddc
    co
    #
    cfz
    co
    #
    wral
    #
    @16
    vm
    vn
    cB
    @17
    c1
    wceq
    @15
    vb
    @18
    @19
    @17
    c1
    c1
    cfz
    oveq2
    raleqdv
    @17
    @20
    wceq
    @15
    vb
    @18
    @21
    @17
    @20
    c1
    cfz
    oveq2
    raleqdv
    @17
    @23
    wceq
    @15
    vb
    @18
    @24
    @17
    @23
    c1
    cfz
    oveq2
    raleqdv
    @17
    cB
    wceq
    @15
    vb
    @18
    @9
    @17
    cB
    c1
    cfz
    oveq2
    raleqdv
    @15
    vb
    @19
    @11
    @19
    wcel
    #
    @14
    va
    cY
    @26
    @13
    @12
    @26
    @11
    c1
    cS
    @11
    c1
    elfz1eq
    c1
    cS
    wcel
    c1
    vx
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
    vx
    cgz
    wrex
    #
    c1
    cgz
    wcel
    #
    c1
    c1
    c2
    cexp
    co
    #
    wceq
    #
    @31
    c1
    cz
    wcel
    @32
    1z
    c1
    zgz
    ax-mp
    @33
    c1
    sq1
    eqcomi
    @30
    @34
    vx
    c1
    cgz
    @27
    c1
    wceq
    #
    @29
    @33
    c1
    @35
    @28
    c1
    c2
    cexp
    @35
    @28
    c1
    cabs
    cfv
    c1
    @27
    c1
    cabs
    fveq2
    abs1
    syl6eq
    oveq1d
    eqeq2d
    rspcev
    mp2an
    vx
    vw
    c1
    cS
    2sq.1
    2sqlem1
    mpbir
    syl6eqel
    a1d
    ralrimivw
    rgen
    @20
    cn
    wcel
    #
    @22
    @22
    @15
    vb
    @23
    csn
    #
    wral
    #
    wa
    #
    @25
    @36
    @22
    @38
    @36
    @22
    @23
    @4
    cdvds
    wbr
    #
    @23
    cS
    wcel
    #
    wi
    #
    va
    cY
    wral
    #
    @38
    @36
    @22
    @23
    @17
    cdvds
    wbr
    #
    @41
    wi
    #
    vm
    cY
    wral
    #
    @43
    @36
    @22
    @46
    @36
    @22
    wa
    #
    @45
    vm
    cY
    @47
    @17
    cY
    wcel
    #
    @44
    @41
    @47
    @48
    @44
    wa
    #
    wa
    #
    vx
    vy
    vz
    vw
    cS
    @23
    @17
    cY
    va
    vb
    2sq.1
    2sqlem7.2
    @50
    @15
    vb
    c1
    @23
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    @22
    @36
    @22
    @49
    simplr
    @50
    @15
    vb
    @52
    @21
    @50
    @51
    @20
    c1
    cfz
    @50
    @20
    cc
    wcel
    #
    c1
    cc
    wcel
    @51
    @20
    wceq
    @36
    @53
    @22
    @49
    @20
    nncn
    ad2antrr
    ax-1cn
    @20
    c1
    pncan
    sylancl
    oveq2d
    raleqdv
    mpbird
    @47
    @48
    @44
    simprr
    @36
    @23
    cn
    wcel
    @22
    @49
    @20
    peano2nn
    ad2antrr
    @47
    @48
    @44
    simprl
    2sqlem9
    expr
    ralrimiva
    ex
    @42
    @45
    va
    vm
    cY
    @4
    @17
    wceq
    @40
    @44
    @41
    @4
    @17
    @23
    cdvds
    breq2
    imbi1d
    cbvralv
    syl6ibr
    @15
    @43
    vb
    @23
    @20
    c1
    caddc
    ovex
    @11
    @23
    wceq
    #
    @14
    @42
    va
    cY
    @54
    @12
    @40
    @13
    @41
    @11
    @23
    @4
    cdvds
    breq1
    @11
    @23
    cS
    eleq1
    imbi12d
    ralbidv
    ralsn
    syl6ibr
    ancld
    @36
    @25
    @15
    vb
    @21
    @37
    cun
    #
    wral
    @39
    @36
    @15
    vb
    @24
    @55
    @36
    @20
    c1
    cuz
    cfv
    wcel
    @24
    @55
    wceq
    @20
    elnnuz
    c1
    @20
    fzsuc
    sylbi
    raleqdv
    @15
    vb
    @21
    @37
    ralunb
    syl6bb
    sylibrd
    nnind
    @15
    @7
    vb
    cB
    @9
    @11
    cB
    wceq
    #
    @14
    @6
    va
    cY
    @56
    @12
    @5
    @13
    @3
    @11
    cB
    @4
    cdvds
    breq1
    @11
    cB
    cS
    eleq1
    imbi12d
    ralbidv
    rspcv
    sylc
    @6
    @8
    va
    cA
    cY
    @4
    cA
    wceq
    @5
    @2
    @3
    @4
    cA
    cB
    cdvds
    breq2
    imbi1d
    rspcv
    syl5
    3imp
end
