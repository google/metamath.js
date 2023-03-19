include "cv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "wa.mm"
include "cz.mm"
include "wrex.mm"
include "wcel.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "2rexbidv.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "cbvrex2v.mm"
include "syl6bb.mm"
include "elab2g.mm"
include "ibi.mm"
include "syl.mm"
include "simpr.mm"
include "cabs.mm"
include "cfv.mm"
include "cgz.mm"
include "1z.mm"
include "zgz.mm"
include "ax-mp.mm"
include "sq1.mm"
include "eqcomi.mm"
include "fveq2.mm"
include "abs1.mm"
include "syl6eq.mm"
include "rspcev.mm"
include "mp2an.mm"
include "2sqlem1.mm"
include "mpbir.mm"
include "syl6eqel.mm"
include "wne.mm"
include "cdiv.mm"
include "cmo.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "cfz.mm"
include "ad2antrr.mm"
include "cn.mm"
include "cin.mm"
include "2sqlem7.mm"
include "inss2.mm"
include "sstri.mm"
include "sseldi.mm"
include "cuz.mm"
include "simprr.mm"
include "eluz2b3.mm"
include "sylanbrc.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprll.mm"
include "simprlr.mm"
include "eqid.mm"
include "2sqlem8.mm"
include "anassrs.mm"
include "pm2.61dane.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem 2sqlem9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cS: class S
  let cM: class M
  let cN: class N
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vm: setvar m
  let cA: class A
  let cC: class C
  let vu: setvar u
  let vv: setvar v
  let cB: class B
  let cD: class D
  let cE: class E
  let cF: class F
  let cP: class P
  assume 2sq.1: |- S = ran ( w e. Z[i] |-> ( ( abs ` w ) ^ 2 ) )
  assume 2sqlem7.2: |- Y = { z | E. x e. ZZ E. y e. ZZ ( ( x gcd y ) = 1 /\ z = ( ( x ^ 2 ) + ( y ^ 2 ) ) ) }
  assume 2sqlem9.5: |- ( ph -> A. b e. ( 1 ... ( M - 1 ) ) A. a e. Y ( b || a -> b e. S ) )
  assume 2sqlem9.7: |- ( ph -> M || N )
  assume 2sqlem9.6: |- ( ph -> M e. NN )
  assume 2sqlem9.4: |- ( ph -> N e. Y )

  disjoint a b
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph x
  disjoint ph y
  disjoint M a
  disjoint M b
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint S a
  disjoint S b
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Y a
  disjoint Y b
  disjoint Y x
  disjoint Y y
  disjoint a n
  disjoint a p
  disjoint a q
  disjoint b n
  disjoint b p
  disjoint b q
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
  disjoint A x
  disjoint A y
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
  disjoint b u
  disjoint b v
  disjoint M p
  disjoint u z
  disjoint M u
  disjoint v z
  disjoint M v
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
  assert |- ( ph -> M e. S )

  proof
    wph
    vu
    cv
    #
    vv
    cv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    cN
    @0
    c2
    cexp
    co
    #
    @1
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    wa
    #
    vv
    cz
    wrex
    vu
    cz
    wrex
    #
    cM
    cS
    wcel
    #
    wph
    cN
    cY
    wcel
    #
    @9
    2sqlem9.4
    @11
    @9
    vx
    cv
    #
    vy
    cv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    vz
    cv
    #
    @12
    c2
    cexp
    co
    #
    @13
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    wa
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    @9
    vz
    cN
    cY
    cY
    @16
    cN
    wceq
    #
    @22
    @15
    cN
    @19
    wceq
    #
    wa
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    @9
    @23
    @21
    @25
    vx
    vy
    cz
    cz
    @23
    @20
    @24
    @15
    @16
    cN
    @19
    eqeq1
    anbi2d
    2rexbidv
    @25
    @8
    @0
    @13
    cgcd
    co
    #
    c1
    wceq
    #
    cN
    @4
    @18
    caddc
    co
    #
    wceq
    #
    wa
    vx
    vy
    vu
    vv
    cz
    cz
    @12
    @0
    wceq
    #
    @15
    @27
    @24
    @29
    @30
    @14
    @26
    c1
    @12
    @0
    @13
    cgcd
    oveq1
    eqeq1d
    @30
    @19
    @28
    cN
    @30
    @17
    @4
    @18
    caddc
    @12
    @0
    c2
    cexp
    oveq1
    oveq1d
    eqeq2d
    anbi12d
    @13
    @1
    wceq
    #
    @27
    @3
    @29
    @7
    @31
    @26
    @2
    c1
    @13
    @1
    @0
    cgcd
    oveq2
    eqeq1d
    @31
    @28
    @6
    cN
    @31
    @18
    @5
    @4
    caddc
    @13
    @1
    c2
    cexp
    oveq1
    oveq2d
    eqeq2d
    anbi12d
    cbvrex2v
    syl6bb
    2sqlem7.2
    elab2g
    ibi
    syl
    wph
    @8
    @10
    vu
    vv
    cz
    cz
    wph
    @0
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    wa
    #
    wa
    #
    @8
    @10
    @35
    @8
    wa
    #
    @10
    cM
    c1
    @36
    cM
    c1
    wceq
    #
    wa
    cM
    c1
    cS
    @36
    @37
    simpr
    c1
    cS
    wcel
    c1
    @12
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
    @41
    c1
    cz
    wcel
    @42
    1z
    c1
    zgz
    ax-mp
    @43
    c1
    sq1
    eqcomi
    @40
    @44
    vx
    c1
    cgz
    @12
    c1
    wceq
    #
    @39
    @43
    c1
    @45
    @38
    c1
    c2
    cexp
    @45
    @38
    c1
    cabs
    cfv
    c1
    @12
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
    @35
    @8
    cM
    c1
    wne
    #
    @10
    @35
    @8
    @46
    wa
    #
    wa
    #
    vx
    vy
    vz
    vw
    @0
    @1
    @0
    cM
    c2
    cdiv
    co
    #
    caddc
    co
    cM
    cmo
    co
    @49
    cmin
    co
    #
    @1
    @49
    caddc
    co
    cM
    cmo
    co
    @49
    cmin
    co
    #
    cS
    @50
    @50
    @51
    cgcd
    co
    #
    cdiv
    co
    #
    @51
    @52
    cdiv
    co
    #
    cM
    cN
    cY
    va
    vb
    2sq.1
    2sqlem7.2
    wph
    vb
    cv
    #
    va
    cv
    cdvds
    wbr
    @55
    cS
    wcel
    wi
    va
    cY
    wral
    vb
    c1
    cM
    c1
    cmin
    co
    cfz
    co
    wral
    @34
    @47
    2sqlem9.5
    ad2antrr
    wph
    cM
    cN
    cdvds
    wbr
    @34
    @47
    2sqlem9.7
    ad2antrr
    wph
    cN
    cn
    wcel
    @34
    @47
    wph
    cY
    cn
    cN
    cY
    cS
    cn
    cin
    cn
    vx
    vy
    vz
    vw
    cS
    cY
    2sq.1
    2sqlem7.2
    2sqlem7
    cS
    cn
    inss2
    sstri
    2sqlem9.4
    sseldi
    ad2antrr
    @48
    cM
    cn
    wcel
    #
    @46
    cM
    c2
    cuz
    cfv
    wcel
    wph
    @56
    @34
    @47
    2sqlem9.6
    ad2antrr
    @35
    @8
    @46
    simprr
    cM
    eluz2b3
    sylanbrc
    wph
    @32
    @33
    @47
    simplrl
    wph
    @32
    @33
    @47
    simplrr
    @35
    @3
    @7
    @46
    simprll
    @35
    @3
    @7
    @46
    simprlr
    @50
    eqid
    @51
    eqid
    @53
    eqid
    @54
    eqid
    2sqlem8
    anassrs
    pm2.61dane
    ex
    rexlimdvva
    mpd
end
