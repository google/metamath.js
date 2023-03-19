include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "cdiv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "wne.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "eluz2b3.mm"
include "sylib.mm"
include "simpld.mm"
include "cz.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cdvds.mm"
include "cgcd.mm"
include "cmul.mm"
include "wceq.mm"
include "cmin.mm"
include "wb.mm"
include "eluzelz.mm"
include "syl.mm"
include "nnzd.mm"
include "4sqlem5.mm"
include "zsqcl.mm"
include "zaddcld.mm"
include "4sqlem8.mm"
include "wi.mm"
include "zsubcld.mm"
include "dvds2add.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "oveq1d.mm"
include "zcnd.mm"
include "addsub4d.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "dvdssub2.mm"
include "syl31anc.mm"
include "mpbid.mm"
include "cn0.mm"
include "2sqlem8a.mm"
include "zsqcl2.mm"
include "nn0cnd.mm"
include "gcddvds.mm"
include "syl2anc.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "syl5eqel.mm"
include "simprd.mm"
include "adddid.mm"
include "sqmuld.mm"
include "oveq2i.mm"
include "divcan2d.mm"
include "syl5eq.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "gcdcom.mm"
include "cle.mm"
include "gcdcld.mm"
include "nn0zd.mm"
include "dvdstr.mm"
include "mpbird.mm"
include "wn.mm"
include "ax-1ne0.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "gcdeq0.mm"
include "mtbid.mm"
include "dvdslegcd.mm"
include "breqtrd.mm"
include "simpr.mm"
include "necon3ai.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "nnle1eq1.mm"
include "2nn.mm"
include "rplpwr.mm"
include "mpd.mm"
include "nn0addcld.mm"
include "coprmdvds.mm"
include "nn0red.mm"
include "readdcld.mm"
include "nnred.mm"
include "cin.mm"
include "2sqlem7.mm"
include "inss2.mm"
include "sstri.mm"
include "cv.mm"
include "wrex.mm"
include "1cnd.mm"
include "mulid1d.mm"
include "mulgcd.mm"
include "3eqtr2rd.mm"
include "mulcanad.mm"
include "eqidd.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "ovex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "2rexbidv.mm"
include "elab2.mm"
include "sylibr.mm"
include "sseldi.mm"
include "nngt0d.mm"
include "divgt0d.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "cprime.mm"
include "cfz.mm"
include "wral.mm"
include "prmnn.mm"
include "ad2antrl.mm"
include "adantr.mm"
include "zred.mm"
include "cr.mm"
include "peano2zm.mm"
include "simprr.mm"
include "prmz.mm"
include "dvdsle.mm"
include "rehalfcld.mm"
include "1red.mm"
include "nnsqcld.mm"
include "nn0ge0d.mm"
include "nnge1d.mm"
include "lemul1ad.mm"
include "mulid2d.mm"
include "3brtr3d.mm"
include "4sqlem7.mm"
include "le2addd.mm"
include "recnd.mm"
include "2halvesd.mm"
include "letrd.mm"
include "crp.mm"
include "nnrpd.mm"
include "rphalflt.mm"
include "lelttrd.mm"
include "sqvald.mm"
include "ltdivmul.mm"
include "zltlem1.mm"
include "fznn.mm"
include "mpbir2and.mm"
include "jca.mm"
include "dvdsmul2.mm"
include "breq1.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "breq2.mm"
include "imbi1d.mm"
include "rspc2v.mm"
include "syl3c.mm"
include "expr.mm"
include "ralrimiva.mm"
include "inss1.mm"
include "eqeltrd.mm"
include "2sqlem6.mm"

theorem 2sqlem8
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cE: class E
  let cF: class F
  let cM: class M
  let cN: class N
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vm: setvar m
  let vu: setvar u
  let vv: setvar v
  let cP: class P
  assume 2sq.1: |- S = ran ( w e. Z[i] |-> ( ( abs ` w ) ^ 2 ) )
  assume 2sqlem7.2: |- Y = { z | E. x e. ZZ E. y e. ZZ ( ( x gcd y ) = 1 /\ z = ( ( x ^ 2 ) + ( y ^ 2 ) ) ) }
  assume 2sqlem9.5: |- ( ph -> A. b e. ( 1 ... ( M - 1 ) ) A. a e. Y ( b || a -> b e. S ) )
  assume 2sqlem9.7: |- ( ph -> M || N )
  assume 2sqlem8.n: |- ( ph -> N e. NN )
  assume 2sqlem8.m: |- ( ph -> M e. ( ZZ>= ` 2 ) )
  assume 2sqlem8.1: |- ( ph -> A e. ZZ )
  assume 2sqlem8.2: |- ( ph -> B e. ZZ )
  assume 2sqlem8.3: |- ( ph -> ( A gcd B ) = 1 )
  assume 2sqlem8.4: |- ( ph -> N = ( ( A ^ 2 ) + ( B ^ 2 ) ) )
  assume 2sqlem8.c: |- C = ( ( ( A + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 2sqlem8.d: |- D = ( ( ( B + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 2sqlem8.e: |- E = ( C / ( C gcd D ) )
  assume 2sqlem8.f: |- F = ( D / ( C gcd D ) )

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
  disjoint A a
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint C x
  disjoint ph x
  disjoint ph y
  disjoint B a
  disjoint B b
  disjoint B x
  disjoint B y
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
  disjoint D x
  disjoint E a
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Y a
  disjoint Y b
  disjoint Y x
  disjoint Y y
  disjoint F a
  disjoint F x
  disjoint F y
  disjoint F z
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
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
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
  disjoint b m
  disjoint m p
  disjoint B m
  disjoint B p
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
  disjoint E p
  disjoint N p
  disjoint N q
  disjoint N u
  disjoint N v
  disjoint Y m
  disjoint Y n
  disjoint F p
  disjoint P n
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint P y
  assert |- ( ph -> M e. S )

  proof
    wph
    vw
    cM
    cE
    c2
    cexp
    co
    #
    cF
    c2
    cexp
    co
    #
    caddc
    co
    #
    cM
    cdiv
    co
    #
    cS
    vp
    2sq.1
    wph
    cM
    cn
    wcel
    #
    cM
    c1
    wne
    #
    wph
    cM
    c2
    cuz
    cfv
    wcel
    #
    @4
    @5
    wa
    2sqlem8.m
    cM
    eluz2b3
    sylib
    simpld
    #
    wph
    @3
    cz
    wcel
    #
    cc0
    @3
    clt
    wbr
    @3
    cn
    wcel
    #
    wph
    cM
    @2
    cdvds
    wbr
    #
    @8
    wph
    cM
    cC
    cD
    cgcd
    co
    #
    c2
    cexp
    co
    #
    @2
    cmul
    co
    #
    cdvds
    wbr
    #
    cM
    @12
    cgcd
    co
    #
    c1
    wceq
    #
    @10
    wph
    cM
    cC
    c2
    cexp
    co
    #
    cD
    c2
    cexp
    co
    #
    caddc
    co
    #
    @13
    cdvds
    wph
    cM
    cN
    cdvds
    wbr
    #
    cM
    @19
    cdvds
    wbr
    #
    2sqlem9.7
    wph
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    @19
    cz
    wcel
    cM
    cN
    @19
    cmin
    co
    #
    cdvds
    wbr
    @20
    @21
    wb
    wph
    @6
    @22
    2sqlem8.m
    c2
    cM
    eluzelz
    syl
    #
    wph
    cN
    2sqlem8.n
    nnzd
    wph
    @17
    @18
    wph
    cC
    cz
    wcel
    #
    @17
    cz
    wcel
    wph
    @25
    cA
    cC
    cmin
    co
    #
    cM
    cdiv
    co
    cz
    wcel
    #
    wph
    cA
    cC
    cM
    2sqlem8.1
    @7
    2sqlem8.c
    4sqlem5
    #
    simpld
    #
    cC
    zsqcl
    syl
    #
    wph
    cD
    cz
    wcel
    #
    @18
    cz
    wcel
    wph
    @31
    cB
    cD
    cmin
    co
    #
    cM
    cdiv
    co
    cz
    wcel
    #
    wph
    cB
    cD
    cM
    2sqlem8.2
    @7
    2sqlem8.d
    4sqlem5
    #
    simpld
    #
    cD
    zsqcl
    syl
    #
    zaddcld
    wph
    cM
    cA
    c2
    cexp
    co
    #
    @17
    cmin
    co
    #
    cB
    c2
    cexp
    co
    #
    @18
    cmin
    co
    #
    caddc
    co
    #
    @23
    cdvds
    wph
    cM
    @38
    cdvds
    wbr
    #
    cM
    @40
    cdvds
    wbr
    #
    cM
    @41
    cdvds
    wbr
    #
    wph
    cA
    cC
    cM
    2sqlem8.1
    @7
    2sqlem8.c
    4sqlem8
    wph
    cB
    cD
    cM
    2sqlem8.2
    @7
    2sqlem8.d
    4sqlem8
    wph
    @22
    @38
    cz
    wcel
    @40
    cz
    wcel
    @42
    @43
    wa
    @44
    wi
    @24
    wph
    @37
    @17
    wph
    cA
    cz
    wcel
    #
    @37
    cz
    wcel
    2sqlem8.1
    cA
    zsqcl
    syl
    #
    @30
    zsubcld
    wph
    @39
    @18
    wph
    cB
    cz
    wcel
    #
    @39
    cz
    wcel
    2sqlem8.2
    cB
    zsqcl
    syl
    #
    @36
    zsubcld
    cM
    @38
    @40
    dvds2add
    syl3anc
    mp2and
    wph
    @23
    @37
    @39
    caddc
    co
    #
    @19
    cmin
    co
    @41
    wph
    cN
    @49
    @19
    cmin
    2sqlem8.4
    oveq1d
    wph
    @37
    @39
    @17
    @18
    wph
    @37
    @46
    zcnd
    wph
    @39
    @48
    zcnd
    wph
    @17
    @30
    zcnd
    wph
    @18
    @36
    zcnd
    addsub4d
    eqtrd
    breqtrrd
    cM
    cN
    @19
    dvdssub2
    syl31anc
    mpbid
    wph
    @13
    @12
    @0
    cmul
    co
    #
    @12
    @1
    cmul
    co
    #
    caddc
    co
    @19
    wph
    @12
    @0
    @1
    wph
    @12
    wph
    @11
    cz
    wcel
    #
    @12
    cn0
    wcel
    wph
    @11
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    cS
    cM
    cN
    cY
    va
    vb
    2sq.1
    2sqlem7.2
    2sqlem9.5
    2sqlem9.7
    2sqlem8.n
    2sqlem8.m
    2sqlem8.1
    2sqlem8.2
    2sqlem8.3
    2sqlem8.4
    2sqlem8.c
    2sqlem8.d
    2sqlem8a
    #
    nnzd
    #
    @11
    zsqcl2
    syl
    nn0cnd
    wph
    @0
    wph
    cE
    cz
    wcel
    #
    @0
    cn0
    wcel
    wph
    cE
    cC
    @11
    cdiv
    co
    #
    cz
    2sqlem8.e
    wph
    @11
    cC
    cdvds
    wbr
    #
    @56
    cz
    wcel
    #
    wph
    @57
    @11
    cD
    cdvds
    wbr
    #
    wph
    @25
    @31
    @57
    @59
    wa
    @29
    @35
    cC
    cD
    gcddvds
    syl2anc
    #
    simpld
    #
    wph
    @52
    @11
    cc0
    wne
    #
    @25
    @57
    @58
    wb
    @54
    wph
    @11
    @53
    nnne0d
    #
    @29
    @11
    cC
    dvdsval2
    syl3anc
    mpbid
    syl5eqel
    #
    cE
    zsqcl2
    syl
    #
    nn0cnd
    wph
    @1
    wph
    cF
    cz
    wcel
    #
    @1
    cn0
    wcel
    wph
    cF
    cD
    @11
    cdiv
    co
    #
    cz
    2sqlem8.f
    wph
    @59
    @67
    cz
    wcel
    #
    wph
    @57
    @59
    @60
    simprd
    #
    wph
    @52
    @62
    @31
    @59
    @68
    wb
    @54
    @63
    @35
    @11
    cD
    dvdsval2
    syl3anc
    mpbid
    syl5eqel
    #
    cF
    zsqcl2
    syl
    #
    nn0cnd
    adddid
    wph
    @50
    @17
    @51
    @18
    caddc
    wph
    @11
    cE
    cmul
    co
    #
    c2
    cexp
    co
    @50
    @17
    wph
    @11
    cE
    wph
    @11
    @54
    zcnd
    #
    wph
    cE
    @64
    zcnd
    sqmuld
    wph
    @72
    cC
    c2
    cexp
    wph
    @72
    @11
    @56
    cmul
    co
    cC
    cE
    @56
    @11
    cmul
    2sqlem8.e
    oveq2i
    wph
    cC
    @11
    wph
    cC
    @29
    zcnd
    @73
    @63
    divcan2d
    syl5eq
    #
    oveq1d
    eqtr3d
    wph
    @11
    cF
    cmul
    co
    #
    c2
    cexp
    co
    @51
    @18
    wph
    @11
    cF
    @73
    wph
    cF
    @70
    zcnd
    sqmuld
    wph
    @75
    cD
    c2
    cexp
    wph
    @75
    @11
    @67
    cmul
    co
    cD
    cF
    @67
    @11
    cmul
    2sqlem8.f
    oveq2i
    wph
    cD
    @11
    wph
    cD
    @35
    zcnd
    @73
    @63
    divcan2d
    syl5eq
    #
    oveq1d
    eqtr3d
    oveq12d
    eqtrd
    #
    breqtrrd
    wph
    @15
    @12
    cM
    cgcd
    co
    #
    c1
    wph
    @22
    @12
    cz
    wcel
    #
    @15
    @78
    wceq
    @24
    wph
    @52
    @79
    @54
    @11
    zsqcl
    syl
    #
    cM
    @12
    gcdcom
    syl2anc
    wph
    @11
    cM
    cgcd
    co
    #
    c1
    wceq
    #
    @78
    c1
    wceq
    #
    wph
    @81
    c1
    cle
    wbr
    #
    @82
    wph
    @81
    cA
    cB
    cgcd
    co
    #
    c1
    cle
    wph
    @81
    cA
    cdvds
    wbr
    #
    @81
    cB
    cdvds
    wbr
    #
    @81
    @85
    cle
    wbr
    #
    wph
    @86
    @81
    cC
    cdvds
    wbr
    #
    wph
    @81
    @11
    cdvds
    wbr
    #
    @57
    @89
    wph
    @90
    @81
    cM
    cdvds
    wbr
    #
    wph
    @52
    @22
    @90
    @91
    wa
    @54
    @24
    @11
    cM
    gcddvds
    syl2anc
    #
    simpld
    #
    @61
    wph
    @81
    cz
    wcel
    #
    @52
    @25
    @90
    @57
    wa
    @89
    wi
    wph
    @81
    wph
    @11
    cM
    @54
    @24
    gcdcld
    nn0zd
    #
    @54
    @29
    @81
    @11
    cC
    dvdstr
    syl3anc
    mp2and
    wph
    @94
    @45
    @25
    @81
    @26
    cdvds
    wbr
    #
    @86
    @89
    wb
    @95
    2sqlem8.1
    @29
    wph
    @91
    cM
    @26
    cdvds
    wbr
    #
    @96
    wph
    @90
    @91
    @92
    simprd
    #
    wph
    @97
    @27
    wph
    @25
    @27
    @28
    simprd
    wph
    @22
    cM
    cc0
    wne
    #
    @26
    cz
    wcel
    #
    @97
    @27
    wb
    @24
    wph
    cM
    @7
    nnne0d
    #
    wph
    cA
    cC
    2sqlem8.1
    @29
    zsubcld
    #
    cM
    @26
    dvdsval2
    syl3anc
    mpbird
    wph
    @94
    @22
    @100
    @91
    @97
    wa
    @96
    wi
    @95
    @24
    @102
    @81
    cM
    @26
    dvdstr
    syl3anc
    mp2and
    @81
    cA
    cC
    dvdssub2
    syl31anc
    mpbird
    wph
    @87
    @81
    cD
    cdvds
    wbr
    #
    wph
    @90
    @59
    @103
    @93
    @69
    wph
    @94
    @52
    @31
    @90
    @59
    wa
    @103
    wi
    @95
    @54
    @35
    @81
    @11
    cD
    dvdstr
    syl3anc
    mp2and
    wph
    @94
    @47
    @31
    @81
    @32
    cdvds
    wbr
    #
    @87
    @103
    wb
    @95
    2sqlem8.2
    @35
    wph
    @91
    cM
    @32
    cdvds
    wbr
    #
    @104
    @98
    wph
    @105
    @33
    wph
    @31
    @33
    @34
    simprd
    wph
    @22
    @99
    @32
    cz
    wcel
    #
    @105
    @33
    wb
    @24
    @101
    wph
    cB
    cD
    2sqlem8.2
    @35
    zsubcld
    #
    cM
    @32
    dvdsval2
    syl3anc
    mpbird
    wph
    @94
    @22
    @106
    @91
    @105
    wa
    @104
    wi
    @95
    @24
    @107
    @81
    cM
    @32
    dvdstr
    syl3anc
    mp2and
    @81
    cB
    cD
    dvdssub2
    syl31anc
    mpbird
    wph
    @94
    @45
    @47
    cA
    cc0
    wceq
    cB
    cc0
    wceq
    wa
    #
    wn
    @86
    @87
    wa
    @88
    wi
    @95
    2sqlem8.1
    2sqlem8.2
    wph
    @85
    cc0
    wceq
    #
    @108
    wph
    @85
    cc0
    wph
    @85
    c1
    cc0
    2sqlem8.3
    c1
    cc0
    wne
    wph
    ax-1ne0
    a1i
    eqnetrd
    neneqd
    wph
    @45
    @47
    @109
    @108
    wb
    2sqlem8.1
    2sqlem8.2
    cA
    cB
    gcdeq0
    syl2anc
    mtbid
    @81
    cA
    cB
    dvdslegcd
    syl31anc
    mp2and
    2sqlem8.3
    breqtrd
    wph
    @81
    cn
    wcel
    #
    @84
    @82
    wb
    wph
    @52
    @22
    @11
    cc0
    wceq
    #
    cM
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @110
    @54
    @24
    wph
    @99
    @114
    @101
    @113
    cM
    cc0
    @111
    @112
    simpr
    necon3ai
    syl
    @11
    cM
    gcdn0cl
    syl21anc
    @81
    nnle1eq1
    syl
    mpbid
    wph
    @11
    cn
    wcel
    @4
    c2
    cn
    wcel
    #
    @82
    @83
    wi
    @53
    @7
    @115
    wph
    2nn
    a1i
    @11
    cM
    c2
    rplpwr
    syl3anc
    mpd
    eqtrd
    wph
    @22
    @79
    @2
    cz
    wcel
    #
    @14
    @16
    wa
    @10
    wi
    @24
    @80
    wph
    @2
    wph
    @0
    @1
    @65
    @71
    nn0addcld
    #
    nn0zd
    #
    cM
    @12
    @2
    coprmdvds
    syl3anc
    mp2and
    wph
    @22
    @99
    @116
    @10
    @8
    wb
    @24
    @101
    @118
    cM
    @2
    dvdsval2
    syl3anc
    mpbid
    #
    wph
    @2
    cM
    wph
    @0
    @1
    wph
    @0
    @65
    nn0red
    wph
    @1
    @71
    nn0red
    readdcld
    #
    wph
    cM
    @7
    nnred
    #
    wph
    @2
    wph
    cY
    cn
    @2
    cY
    cS
    cn
    cin
    #
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
    #
    cS
    cn
    inss2
    sstri
    wph
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
    @2
    @124
    c2
    cexp
    co
    #
    @125
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
    @2
    cY
    wcel
    #
    wph
    @55
    @66
    cE
    cF
    cgcd
    co
    #
    c1
    wceq
    #
    @2
    @2
    wceq
    #
    @133
    @64
    @70
    wph
    @135
    c1
    @11
    wph
    @135
    wph
    cE
    cF
    @64
    @70
    gcdcld
    nn0cnd
    wph
    1cnd
    @73
    @63
    wph
    @11
    c1
    cmul
    co
    @11
    @72
    @75
    cgcd
    co
    #
    @11
    @135
    cmul
    co
    #
    wph
    @11
    @73
    mulid1d
    wph
    @72
    cC
    @75
    cD
    cgcd
    @74
    @76
    oveq12d
    wph
    @11
    cn0
    wcel
    @55
    @66
    @138
    @139
    wceq
    wph
    cC
    cD
    @29
    @35
    gcdcld
    @64
    @70
    @11
    cE
    cF
    mulgcd
    syl3anc
    3eqtr2rd
    mulcanad
    wph
    @2
    eqidd
    @132
    @136
    @137
    wa
    cE
    @125
    cgcd
    co
    #
    c1
    wceq
    #
    @2
    @0
    @129
    caddc
    co
    #
    wceq
    #
    wa
    vx
    vy
    cE
    cF
    cz
    cz
    @124
    cE
    wceq
    #
    @127
    @141
    @131
    @143
    @144
    @126
    @140
    c1
    @124
    cE
    @125
    cgcd
    oveq1
    eqeq1d
    @144
    @130
    @142
    @2
    @144
    @128
    @0
    @129
    caddc
    @124
    cE
    c2
    cexp
    oveq1
    oveq1d
    eqeq2d
    anbi12d
    @125
    cF
    wceq
    #
    @141
    @136
    @143
    @137
    @145
    @140
    @135
    c1
    @125
    cF
    cE
    cgcd
    oveq2
    eqeq1d
    @145
    @142
    @2
    @2
    @145
    @129
    @1
    @0
    caddc
    @125
    cF
    c2
    cexp
    oveq1
    oveq2d
    eqeq2d
    anbi12d
    rspc2ev
    syl112anc
    @127
    vz
    cv
    #
    @130
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
    @133
    vz
    @2
    cY
    @0
    @1
    caddc
    ovex
    @146
    @2
    wceq
    #
    @148
    @132
    vx
    vy
    cz
    cz
    @149
    @147
    @131
    @127
    @146
    @2
    @130
    eqeq1
    anbi2d
    2rexbidv
    2sqlem7.2
    elab2
    sylibr
    #
    sseldi
    nngt0d
    wph
    cM
    @7
    nngt0d
    #
    divgt0d
    @3
    elnnz
    sylanbrc
    #
    wph
    vp
    cv
    #
    @3
    cdvds
    wbr
    #
    @153
    cS
    wcel
    #
    wi
    vp
    cprime
    wph
    @153
    cprime
    wcel
    #
    @154
    @155
    wph
    @156
    @154
    wa
    #
    wa
    #
    @153
    c1
    cM
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    @134
    wa
    vb
    cv
    #
    va
    cv
    #
    cdvds
    wbr
    #
    @162
    cS
    wcel
    #
    wi
    #
    va
    cY
    wral
    vb
    @160
    wral
    #
    @153
    @2
    cdvds
    wbr
    #
    @155
    @158
    @161
    @134
    @158
    @161
    @153
    cn
    wcel
    #
    @153
    @159
    cle
    wbr
    #
    @156
    @169
    wph
    @154
    @153
    prmnn
    ad2antrl
    #
    @158
    @153
    @3
    @159
    @158
    @153
    @171
    nnred
    @158
    @3
    wph
    @8
    @157
    @119
    adantr
    #
    zred
    wph
    @159
    cr
    wcel
    @157
    wph
    @159
    wph
    @22
    @159
    cz
    wcel
    #
    @24
    cM
    peano2zm
    syl
    #
    zred
    adantr
    @158
    @154
    @153
    @3
    cle
    wbr
    #
    wph
    @156
    @154
    simprr
    #
    @158
    @153
    cz
    wcel
    #
    @9
    @154
    @175
    wi
    @156
    @177
    wph
    @154
    @153
    prmz
    ad2antrl
    #
    wph
    @9
    @157
    @152
    adantr
    @153
    @3
    dvdsle
    syl2anc
    mpd
    wph
    @3
    @159
    cle
    wbr
    #
    @157
    wph
    @3
    cM
    clt
    wbr
    #
    @179
    wph
    @180
    @2
    cM
    cM
    cmul
    co
    #
    clt
    wbr
    #
    wph
    @2
    cM
    c2
    cexp
    co
    #
    @181
    clt
    wph
    @2
    @183
    c2
    cdiv
    co
    #
    @183
    @120
    wph
    @183
    wph
    @183
    wph
    @22
    @183
    cz
    wcel
    @24
    cM
    zsqcl
    syl
    zred
    #
    rehalfcld
    #
    @185
    wph
    @2
    @19
    @184
    @120
    wph
    @17
    @18
    wph
    @17
    @30
    zred
    #
    wph
    @18
    @36
    zred
    #
    readdcld
    @186
    wph
    c1
    @2
    cmul
    co
    @13
    @2
    @19
    cle
    wph
    c1
    @12
    @2
    wph
    1red
    wph
    @12
    wph
    @11
    @53
    nnsqcld
    #
    nnred
    @120
    wph
    @2
    @117
    nn0ge0d
    wph
    @12
    @189
    nnge1d
    lemul1ad
    wph
    @2
    wph
    @2
    @117
    nn0cnd
    #
    mulid2d
    @77
    3brtr3d
    wph
    @19
    @184
    c2
    cdiv
    co
    #
    @191
    caddc
    co
    @184
    cle
    wph
    @17
    @18
    @191
    @191
    @187
    @188
    wph
    @184
    @186
    rehalfcld
    #
    @192
    wph
    cA
    cC
    cM
    2sqlem8.1
    @7
    2sqlem8.c
    4sqlem7
    wph
    cB
    cD
    cM
    2sqlem8.2
    @7
    2sqlem8.d
    4sqlem7
    le2addd
    wph
    @184
    wph
    @184
    @186
    recnd
    2halvesd
    breqtrd
    letrd
    wph
    @183
    crp
    wcel
    @184
    @183
    clt
    wbr
    wph
    @183
    wph
    cM
    @7
    nnsqcld
    nnrpd
    @183
    rphalflt
    syl
    lelttrd
    wph
    cM
    wph
    cM
    @24
    zcnd
    #
    sqvald
    breqtrd
    wph
    @2
    cr
    wcel
    cM
    cr
    wcel
    #
    @194
    cc0
    cM
    clt
    wbr
    @180
    @182
    wb
    @120
    @121
    @121
    @151
    @2
    cM
    cM
    ltdivmul
    syl112anc
    mpbird
    wph
    @8
    @22
    @180
    @179
    wb
    @119
    @24
    @3
    cM
    zltlem1
    syl2anc
    mpbid
    adantr
    letrd
    @158
    @173
    @161
    @169
    @170
    wa
    wb
    wph
    @173
    @157
    @174
    adantr
    @153
    @159
    fznn
    syl
    mpbir2and
    wph
    @134
    @157
    @150
    adantr
    jca
    wph
    @167
    @157
    2sqlem9.5
    adantr
    @158
    @154
    @3
    @2
    cdvds
    wbr
    #
    @168
    @176
    wph
    @195
    @157
    wph
    @3
    cM
    @3
    cmul
    co
    #
    @2
    cdvds
    wph
    @22
    @8
    @3
    @196
    cdvds
    wbr
    @24
    @119
    cM
    @3
    dvdsmul2
    syl2anc
    wph
    @2
    cM
    @190
    @193
    @101
    divcan2d
    #
    breqtrd
    adantr
    @158
    @177
    @8
    @116
    @154
    @195
    wa
    @168
    wi
    @178
    @172
    wph
    @116
    @157
    @118
    adantr
    @153
    @3
    @2
    dvdstr
    syl3anc
    mp2and
    @166
    @168
    @155
    wi
    @153
    @163
    cdvds
    wbr
    #
    @155
    wi
    vb
    va
    @153
    @2
    @160
    cY
    @162
    @153
    wceq
    @164
    @198
    @165
    @155
    @162
    @153
    @163
    cdvds
    breq1
    @162
    @153
    cS
    eleq1
    imbi12d
    @163
    @2
    wceq
    @198
    @168
    @155
    @163
    @2
    @153
    cdvds
    breq2
    imbi1d
    rspc2v
    syl3c
    expr
    ralrimiva
    wph
    @196
    @2
    cS
    @197
    wph
    cY
    cS
    @2
    cY
    @122
    cS
    @123
    cS
    cn
    inss1
    sstri
    @150
    sseldi
    eqeltrd
    2sqlem6
end
