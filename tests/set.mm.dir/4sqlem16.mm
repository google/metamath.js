include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cdvds.mm"
include "wi.mm"
include "caddc.mm"
include "cdiv.mm"
include "cz.mm"
include "wcel.mm"
include "cmin.mm"
include "cuz.mm"
include "cfv.mm"
include "cn.mm"
include "eluz2nn.mm"
include "syl.mm"
include "4sqlem5.mm"
include "simpld.mm"
include "zsqcl.mm"
include "zred.mm"
include "readdcld.mm"
include "nnred.mm"
include "resqcld.mm"
include "rehalfcld.mm"
include "4sqlem7.mm"
include "le2addd.mm"
include "recnd.mm"
include "2halvesd.mm"
include "breqtrd.mm"
include "sqvald.mm"
include "cr.mm"
include "clt.mm"
include "wb.mm"
include "nngt0d.mm"
include "ledivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "syl5eqbr.mm"
include "wa.mm"
include "simpr.mm"
include "syl5eqr.mm"
include "nnne0d.mm"
include "diveq0ad.mm"
include "cn0.mm"
include "zsqcl2.mm"
include "nn0addcld.mm"
include "nn0ge0d.mm"
include "add20.mm"
include "syl22anc.mm"
include "bitrd.mm"
include "biimpa.mm"
include "syldan.mm"
include "4sqlem9.mm"
include "simprd.mm"
include "nnsqcld.mm"
include "nnzd.mm"
include "dvds2add.mm"
include "syl3anc.mm"
include "adantr.mm"
include "mp2and.mm"
include "zaddcld.mm"
include "4sqlem15.mm"
include "4sqlem10.mm"
include "zcnd.mm"
include "subeq0ad.mm"
include "mpbid.mm"
include "eqeltrd.mm"
include "zsubcld.mm"
include "addsub4d.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "eqeltrrd.mm"
include "dvdssubr.mm"
include "syl2anc.mm"
include "jaodan.mm"
include "breqtrrd.mm"
include "ex.mm"
include "jca.mm"

theorem 4sqlem16
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vk: setvar k
  let vv: setvar v
  let vu: setvar u
  let vm: setvar m
  assume 4sq.1: |- S = { n | E. x e. ZZ E. y e. ZZ E. z e. ZZ E. w e. ZZ n = ( ( ( x ^ 2 ) + ( y ^ 2 ) ) + ( ( z ^ 2 ) + ( w ^ 2 ) ) ) }
  assume 4sq.2: |- ( ph -> N e. NN )
  assume 4sq.3: |- ( ph -> P = ( ( 2 x. N ) + 1 ) )
  assume 4sq.4: |- ( ph -> P e. Prime )
  assume 4sq.5: |- ( ph -> ( 0 ... ( 2 x. N ) ) C_ S )
  assume 4sq.6: |- T = { i e. NN | ( i x. P ) e. S }
  assume 4sq.7: |- M = inf ( T , RR , < )
  assume 4sq.m: |- ( ph -> M e. ( ZZ>= ` 2 ) )
  assume 4sq.a: |- ( ph -> A e. ZZ )
  assume 4sq.b: |- ( ph -> B e. ZZ )
  assume 4sq.c: |- ( ph -> C e. ZZ )
  assume 4sq.d: |- ( ph -> D e. ZZ )
  assume 4sq.e: |- E = ( ( ( A + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sq.f: |- F = ( ( ( B + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sq.g: |- G = ( ( ( C + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sq.h: |- H = ( ( ( D + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sq.r: |- R = ( ( ( ( E ^ 2 ) + ( F ^ 2 ) ) + ( ( G ^ 2 ) + ( H ^ 2 ) ) ) / M )
  assume 4sq.p: |- ( ph -> ( M x. P ) = ( ( ( A ^ 2 ) + ( B ^ 2 ) ) + ( ( C ^ 2 ) + ( D ^ 2 ) ) ) )

  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B n
  disjoint E n
  disjoint G n
  disjoint H n
  disjoint A n
  disjoint C n
  disjoint D n
  disjoint F n
  disjoint i n
  disjoint M i
  disjoint M n
  disjoint N n
  disjoint P i
  disjoint P n
  disjoint n ph
  disjoint S i
  disjoint S n
  disjoint R i
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a n
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b d
  disjoint b n
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c d
  disjoint c n
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d n
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint a j
  disjoint a k
  disjoint a v
  disjoint A a
  disjoint b j
  disjoint b k
  disjoint b v
  disjoint A b
  disjoint c j
  disjoint c k
  disjoint c v
  disjoint A c
  disjoint d j
  disjoint d k
  disjoint d v
  disjoint A d
  disjoint j k
  disjoint j n
  disjoint j v
  disjoint A j
  disjoint k n
  disjoint k v
  disjoint A k
  disjoint n v
  disjoint A v
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint F j
  disjoint a i
  disjoint a u
  disjoint M a
  disjoint b i
  disjoint b u
  disjoint M b
  disjoint c i
  disjoint c u
  disjoint M c
  disjoint d i
  disjoint d u
  disjoint M d
  disjoint i k
  disjoint i u
  disjoint k u
  disjoint M k
  disjoint n u
  disjoint M u
  disjoint k m
  disjoint N k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint N m
  disjoint u v
  disjoint N u
  disjoint N v
  disjoint a m
  disjoint P a
  disjoint b m
  disjoint P b
  disjoint c m
  disjoint P c
  disjoint d m
  disjoint P d
  disjoint i j
  disjoint i m
  disjoint i v
  disjoint j m
  disjoint j u
  disjoint P j
  disjoint P k
  disjoint P m
  disjoint P u
  disjoint P v
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph u
  disjoint ph v
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S u
  disjoint S v
  disjoint T k
  disjoint T u
  assert |- ( ph -> ( R <_ M /\ ( ( R = 0 \/ R = M ) -> ( M ^ 2 ) || ( M x. P ) ) ) )

  proof
    wph
    cR
    cM
    cle
    wbr
    cR
    cc0
    wceq
    #
    cR
    cM
    wceq
    #
    wo
    #
    cM
    c2
    cexp
    co
    #
    cM
    cP
    cmul
    co
    #
    cdvds
    wbr
    #
    wi
    wph
    cR
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
    cG
    c2
    cexp
    co
    #
    cH
    c2
    cexp
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    cM
    cdiv
    co
    #
    cM
    cle
    4sq.r
    wph
    @13
    cM
    cle
    wbr
    #
    @12
    cM
    cM
    cmul
    co
    #
    cle
    wbr
    #
    wph
    @12
    @3
    @15
    cle
    wph
    @12
    @3
    c2
    cdiv
    co
    #
    @17
    caddc
    co
    #
    @3
    cle
    wph
    @8
    @11
    @17
    @17
    wph
    @6
    @7
    wph
    @6
    wph
    cE
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    wph
    @19
    cA
    cE
    cmin
    co
    cM
    cdiv
    co
    cz
    wcel
    wph
    cA
    cE
    cM
    4sq.a
    wph
    cM
    c2
    cuz
    cfv
    wcel
    cM
    cn
    wcel
    4sq.m
    cM
    eluz2nn
    syl
    #
    4sq.e
    4sqlem5
    simpld
    #
    cE
    zsqcl
    syl
    #
    zred
    #
    wph
    @7
    wph
    cF
    cz
    wcel
    #
    @7
    cz
    wcel
    wph
    @25
    cB
    cF
    cmin
    co
    cM
    cdiv
    co
    cz
    wcel
    wph
    cB
    cF
    cM
    4sq.b
    @21
    4sq.f
    4sqlem5
    simpld
    #
    cF
    zsqcl
    syl
    zred
    #
    readdcld
    #
    wph
    @9
    @10
    wph
    @9
    wph
    cG
    cz
    wcel
    #
    @9
    cz
    wcel
    wph
    @29
    cC
    cG
    cmin
    co
    cM
    cdiv
    co
    cz
    wcel
    wph
    cC
    cG
    cM
    4sq.c
    @21
    4sq.g
    4sqlem5
    simpld
    #
    cG
    zsqcl
    syl
    zred
    #
    wph
    @10
    wph
    cH
    cz
    wcel
    #
    @10
    cz
    wcel
    wph
    @32
    cD
    cH
    cmin
    co
    cM
    cdiv
    co
    cz
    wcel
    wph
    cD
    cH
    cM
    4sq.d
    @21
    4sq.h
    4sqlem5
    simpld
    #
    cH
    zsqcl
    syl
    zred
    #
    readdcld
    #
    wph
    @3
    wph
    cM
    wph
    cM
    @21
    nnred
    #
    resqcld
    #
    rehalfcld
    #
    @38
    wph
    @8
    @17
    c2
    cdiv
    co
    #
    @39
    caddc
    co
    #
    @17
    cle
    wph
    @6
    @7
    @39
    @39
    @24
    @27
    wph
    @17
    @38
    rehalfcld
    #
    @41
    wph
    cA
    cE
    cM
    4sq.a
    @21
    4sq.e
    4sqlem7
    wph
    cB
    cF
    cM
    4sq.b
    @21
    4sq.f
    4sqlem7
    le2addd
    wph
    @17
    wph
    @17
    @38
    recnd
    #
    2halvesd
    #
    breqtrd
    wph
    @11
    @40
    @17
    cle
    wph
    @9
    @10
    @39
    @39
    @31
    @34
    @41
    @41
    wph
    cC
    cG
    cM
    4sq.c
    @21
    4sq.g
    4sqlem7
    wph
    cD
    cH
    cM
    4sq.d
    @21
    4sq.h
    4sqlem7
    le2addd
    @43
    breqtrd
    le2addd
    wph
    @3
    wph
    @3
    @37
    recnd
    2halvesd
    #
    breqtrd
    wph
    cM
    wph
    cM
    @36
    recnd
    #
    sqvald
    breqtrd
    wph
    @12
    cr
    wcel
    cM
    cr
    wcel
    #
    @46
    cc0
    cM
    clt
    wbr
    @14
    @16
    wb
    wph
    @8
    @11
    @28
    @35
    readdcld
    #
    @36
    @36
    wph
    cM
    @21
    nngt0d
    @12
    cM
    cM
    ledivmul
    syl112anc
    mpbird
    syl5eqbr
    wph
    @2
    @5
    wph
    @2
    wa
    @3
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
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
    caddc
    co
    #
    @4
    cdvds
    wph
    @0
    @3
    @54
    cdvds
    wbr
    #
    @1
    wph
    @0
    wa
    #
    @3
    @50
    cdvds
    wbr
    #
    @3
    @53
    cdvds
    wbr
    #
    @55
    @56
    @3
    @48
    cdvds
    wbr
    #
    @3
    @49
    cdvds
    wbr
    #
    @57
    wph
    @0
    cA
    cE
    cM
    4sq.a
    @21
    4sq.e
    @56
    @6
    cc0
    wceq
    #
    @7
    cc0
    wceq
    #
    wph
    @0
    @8
    cc0
    wceq
    #
    @61
    @62
    wa
    #
    @56
    @63
    @11
    cc0
    wceq
    #
    wph
    @0
    @13
    cc0
    wceq
    #
    @63
    @65
    wa
    #
    @56
    @13
    cR
    cc0
    4sq.r
    wph
    @0
    simpr
    syl5eqr
    wph
    @66
    @67
    wph
    @66
    @12
    cc0
    wceq
    #
    @67
    wph
    @12
    cM
    wph
    @12
    @47
    recnd
    @45
    wph
    cM
    @21
    nnne0d
    diveq0ad
    wph
    @8
    cr
    wcel
    cc0
    @8
    cle
    wbr
    @11
    cr
    wcel
    cc0
    @11
    cle
    wbr
    @68
    @67
    wb
    @28
    wph
    @8
    wph
    @6
    @7
    wph
    @19
    @6
    cn0
    wcel
    @22
    cE
    zsqcl2
    syl
    #
    wph
    @25
    @7
    cn0
    wcel
    @26
    cF
    zsqcl2
    syl
    #
    nn0addcld
    nn0ge0d
    @35
    wph
    @11
    wph
    @9
    @10
    wph
    @29
    @9
    cn0
    wcel
    @30
    cG
    zsqcl2
    syl
    #
    wph
    @32
    @10
    cn0
    wcel
    @33
    cH
    zsqcl2
    syl
    #
    nn0addcld
    nn0ge0d
    @8
    @11
    add20
    syl22anc
    bitrd
    biimpa
    syldan
    #
    simpld
    wph
    @63
    @64
    wph
    @6
    cr
    wcel
    cc0
    @6
    cle
    wbr
    @7
    cr
    wcel
    cc0
    @7
    cle
    wbr
    @63
    @64
    wb
    @24
    wph
    @6
    @69
    nn0ge0d
    @27
    wph
    @7
    @70
    nn0ge0d
    @6
    @7
    add20
    syl22anc
    biimpa
    syldan
    #
    simpld
    4sqlem9
    wph
    @0
    cB
    cF
    cM
    4sq.b
    @21
    4sq.f
    @56
    @61
    @62
    @74
    simprd
    4sqlem9
    wph
    @59
    @60
    wa
    @57
    wi
    #
    @0
    wph
    @3
    cz
    wcel
    #
    @48
    cz
    wcel
    #
    @49
    cz
    wcel
    #
    @75
    wph
    @3
    wph
    cM
    @21
    nnsqcld
    nnzd
    #
    wph
    cA
    cz
    wcel
    @77
    4sq.a
    cA
    zsqcl
    syl
    #
    wph
    cB
    cz
    wcel
    @78
    4sq.b
    cB
    zsqcl
    syl
    #
    @3
    @48
    @49
    dvds2add
    syl3anc
    adantr
    mp2and
    @56
    @3
    @51
    cdvds
    wbr
    #
    @3
    @52
    cdvds
    wbr
    #
    @58
    wph
    @0
    cC
    cG
    cM
    4sq.c
    @21
    4sq.g
    @56
    @9
    cc0
    wceq
    #
    @10
    cc0
    wceq
    #
    wph
    @0
    @65
    @84
    @85
    wa
    #
    @56
    @63
    @65
    @73
    simprd
    wph
    @65
    @86
    wph
    @9
    cr
    wcel
    cc0
    @9
    cle
    wbr
    @10
    cr
    wcel
    cc0
    @10
    cle
    wbr
    @65
    @86
    wb
    @31
    wph
    @9
    @71
    nn0ge0d
    @34
    wph
    @10
    @72
    nn0ge0d
    @9
    @10
    add20
    syl22anc
    biimpa
    syldan
    #
    simpld
    4sqlem9
    wph
    @0
    cD
    cH
    cM
    4sq.d
    @21
    4sq.h
    @56
    @84
    @85
    @87
    simprd
    4sqlem9
    wph
    @82
    @83
    wa
    @58
    wi
    #
    @0
    wph
    @76
    @51
    cz
    wcel
    #
    @52
    cz
    wcel
    #
    @88
    @79
    wph
    cC
    cz
    wcel
    @89
    4sq.c
    cC
    zsqcl
    syl
    #
    wph
    cD
    cz
    wcel
    @90
    4sq.d
    cD
    zsqcl
    syl
    #
    @3
    @51
    @52
    dvds2add
    syl3anc
    adantr
    mp2and
    wph
    @57
    @58
    wa
    @55
    wi
    #
    @0
    wph
    @76
    @50
    cz
    wcel
    #
    @53
    cz
    wcel
    #
    @93
    @79
    wph
    @48
    @49
    @80
    @81
    zaddcld
    #
    wph
    @51
    @52
    @91
    @92
    zaddcld
    #
    @3
    @50
    @53
    dvds2add
    syl3anc
    adantr
    mp2and
    wph
    @1
    wa
    #
    @55
    @3
    @54
    @3
    cmin
    co
    #
    cdvds
    wbr
    #
    @98
    @3
    @50
    @17
    cmin
    co
    #
    @53
    @17
    cmin
    co
    #
    caddc
    co
    #
    @99
    cdvds
    @98
    @3
    @101
    cdvds
    wbr
    #
    @3
    @102
    cdvds
    wbr
    #
    @3
    @103
    cdvds
    wbr
    #
    @98
    @3
    @48
    @39
    cmin
    co
    #
    @49
    @39
    cmin
    co
    #
    caddc
    co
    #
    @101
    cdvds
    @98
    @3
    @107
    cdvds
    wbr
    #
    @3
    @108
    cdvds
    wbr
    #
    @3
    @109
    cdvds
    wbr
    #
    wph
    @1
    cA
    cE
    cM
    4sq.a
    @21
    4sq.e
    @98
    @39
    @6
    cmin
    co
    cc0
    wceq
    #
    @39
    @7
    cmin
    co
    cc0
    wceq
    #
    @98
    @113
    @114
    wa
    #
    @39
    @9
    cmin
    co
    cc0
    wceq
    #
    @39
    @10
    cmin
    co
    cc0
    wceq
    #
    wa
    #
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    cP
    cR
    cS
    cT
    vi
    vn
    cE
    cF
    cG
    cH
    cM
    cN
    4sq.1
    4sq.2
    4sq.3
    4sq.4
    4sq.5
    4sq.6
    4sq.7
    4sq.m
    4sq.a
    4sq.b
    4sq.c
    4sq.d
    4sq.e
    4sq.f
    4sq.g
    4sq.h
    4sq.r
    4sq.p
    4sqlem15
    #
    simpld
    #
    simpld
    #
    4sqlem10
    wph
    @1
    cB
    cF
    cM
    4sq.b
    @21
    4sq.f
    @98
    @113
    @114
    @120
    simprd
    4sqlem10
    @98
    @76
    @107
    cz
    wcel
    @108
    cz
    wcel
    @110
    @111
    wa
    @112
    wi
    wph
    @76
    @1
    @79
    adantr
    #
    @98
    @48
    @39
    wph
    @77
    @1
    @80
    adantr
    @98
    @39
    @6
    cz
    @98
    @113
    @39
    @6
    wceq
    #
    @121
    wph
    @113
    @123
    wb
    @1
    wph
    @39
    @6
    wph
    @39
    @41
    recnd
    #
    wph
    @6
    @23
    zcnd
    subeq0ad
    adantr
    mpbid
    wph
    @20
    @1
    @23
    adantr
    eqeltrd
    #
    zsubcld
    @98
    @49
    @39
    wph
    @78
    @1
    @81
    adantr
    @125
    zsubcld
    @3
    @107
    @108
    dvds2add
    syl3anc
    mp2and
    wph
    @109
    @101
    wceq
    @1
    wph
    @50
    @40
    cmin
    co
    @109
    @101
    wph
    @48
    @49
    @39
    @39
    wph
    @48
    @80
    zcnd
    wph
    @49
    @81
    zcnd
    @124
    @124
    addsub4d
    wph
    @40
    @17
    @50
    cmin
    @43
    oveq2d
    eqtr3d
    adantr
    breqtrd
    @98
    @3
    @51
    @39
    cmin
    co
    #
    @52
    @39
    cmin
    co
    #
    caddc
    co
    #
    @102
    cdvds
    @98
    @3
    @126
    cdvds
    wbr
    #
    @3
    @127
    cdvds
    wbr
    #
    @3
    @128
    cdvds
    wbr
    #
    wph
    @1
    cC
    cG
    cM
    4sq.c
    @21
    4sq.g
    @98
    @116
    @117
    @98
    @115
    @118
    @119
    simprd
    #
    simpld
    4sqlem10
    wph
    @1
    cD
    cH
    cM
    4sq.d
    @21
    4sq.h
    @98
    @116
    @117
    @132
    simprd
    4sqlem10
    @98
    @76
    @126
    cz
    wcel
    @127
    cz
    wcel
    @129
    @130
    wa
    @131
    wi
    @122
    @98
    @51
    @39
    wph
    @89
    @1
    @91
    adantr
    @125
    zsubcld
    @98
    @52
    @39
    wph
    @90
    @1
    @92
    adantr
    @125
    zsubcld
    @3
    @126
    @127
    dvds2add
    syl3anc
    mp2and
    wph
    @128
    @102
    wceq
    @1
    wph
    @53
    @40
    cmin
    co
    @128
    @102
    wph
    @51
    @52
    @39
    @39
    wph
    @51
    @91
    zcnd
    wph
    @52
    @92
    zcnd
    @124
    @124
    addsub4d
    wph
    @40
    @17
    @53
    cmin
    @43
    oveq2d
    eqtr3d
    adantr
    breqtrd
    @98
    @76
    @101
    cz
    wcel
    @102
    cz
    wcel
    @104
    @105
    wa
    @106
    wi
    @122
    @98
    @50
    @17
    wph
    @94
    @1
    @96
    adantr
    @98
    @40
    @17
    cz
    wph
    @40
    @17
    wceq
    @1
    @43
    adantr
    @98
    @39
    @39
    @125
    @125
    zaddcld
    eqeltrrd
    #
    zsubcld
    @98
    @53
    @17
    wph
    @95
    @1
    @97
    adantr
    @133
    zsubcld
    @3
    @101
    @102
    dvds2add
    syl3anc
    mp2and
    wph
    @103
    @99
    wceq
    @1
    wph
    @54
    @18
    cmin
    co
    @103
    @99
    wph
    @50
    @53
    @17
    @17
    wph
    @50
    @96
    zcnd
    wph
    @53
    @97
    zcnd
    @42
    @42
    addsub4d
    wph
    @18
    @3
    @54
    cmin
    @44
    oveq2d
    eqtr3d
    adantr
    breqtrd
    @98
    @76
    @54
    cz
    wcel
    #
    @55
    @100
    wb
    @122
    wph
    @134
    @1
    wph
    @50
    @53
    @96
    @97
    zaddcld
    adantr
    @3
    @54
    dvdssubr
    syl2anc
    mpbird
    jaodan
    wph
    @4
    @54
    wceq
    @2
    4sq.p
    adantr
    breqtrrd
    ex
    jca
end
