include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "ccxp.mm"
include "co.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "cle.mm"
include "cr.mm"
include "cq.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cuz.mm"
include "eluz2b2.mm"
include "sylib.mm"
include "simpld.mm"
include "nnq.mm"
include "syl.mm"
include "qrngbas.mm"
include "abvcl.mm"
include "syl2anc.mm"
include "adantr.mm"
include "recnd.mm"
include "cif.mm"
include "1re.mm"
include "ifcl.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "cc0.mm"
include "0red.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "max2.mm"
include "syl6breqr.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "rpge0d.mm"
include "clog.mm"
include "crp.mm"
include "nnred.mm"
include "simprd.mm"
include "rplogcld.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "recxpcld.mm"
include "rpcxpcld.mm"
include "rpne0d.mm"
include "cn0.mm"
include "nnnn0.mm"
include "adantl.mm"
include "expdivd.mm"
include "cfl.mm"
include "reexpcl.mm"
include "syl2an.mm"
include "nnre.mm"
include "remulcld.mm"
include "nn0ge0d.mm"
include "mulge0d.mm"
include "flge0nn0.mm"
include "peano2nn0.mm"
include "nn0red.mm"
include "reexpcld.mm"
include "peano2re.mm"
include "wceq.mm"
include "qabvexp.mm"
include "syl3anc.mm"
include "cmin.mm"
include "cfz.mm"
include "ce.mm"
include "cc.mm"
include "divassd.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "mulcld.mm"
include "divcan1d.mm"
include "eqtr3d.mm"
include "flltp1.mm"
include "ltmul1dd.mm"
include "eqbrtrrd.mm"
include "wb.mm"
include "eflt.mm"
include "mpbid.mm"
include "cz.mm"
include "nnrpd.mm"
include "nnz.mm"
include "reexplog.mm"
include "nn0zd.mm"
include "3brtr4d.mm"
include "nnexpcl.mm"
include "nnexpcld.mm"
include "nnltlem1.mm"
include "nnnn0d.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nnzd.mm"
include "peano2zm.mm"
include "elfz5.mm"
include "mpbird.mm"
include "wi.mm"
include "ostth2lem2.mm"
include "3expia.mm"
include "syldan.mm"
include "mpd.mm"
include "flle.mm"
include "leadd1dd.mm"
include "nnge1.mm"
include "leadd2dd.mm"
include "adddid.mm"
include "mulid1d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "letrd.mm"
include "nngt0d.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "expgt0.mm"
include "lemul1.mm"
include "expp1d.mm"
include "remulcl.mm"
include "mulcomd.mm"
include "breqtrd.mm"
include "cxplead.mm"
include "cxpexp.mm"
include "cxpmuld.mm"
include "3brtr3d.mm"
include "lemul1d.mm"
include "eqbrtrd.mm"
include "nngt0.mm"
include "rpgt0d.mm"
include "ltp1d.mm"
include "lttrd.mm"
include "mulgt0d.mm"
include "mul12d.mm"
include "mul32d.mm"
include "rpexpcld.mm"
include "ledivmuld.mm"

theorem ostth2lem3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let vq: setvar q
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let cY: class Y
  let cP: class P
  assume qrng.q: |- Q = ( CCfld |`s QQ )
  assume qabsabv.a: |- A = ( AbsVal ` Q )
  assume padic.j: |- J = ( q e. Prime |-> ( x e. QQ |-> if ( x = 0 , 0 , ( q ^ -u ( q pCnt x ) ) ) ) )
  assume ostth.k: |- K = ( x e. QQ |-> if ( x = 0 , 0 , 1 ) )
  assume ostth.1: |- ( ph -> F e. A )
  assume ostth2.2: |- ( ph -> N e. ( ZZ>= ` 2 ) )
  assume ostth2.3: |- ( ph -> 1 < ( F ` N ) )
  assume ostth2.4: |- R = ( ( log ` ( F ` N ) ) / ( log ` N ) )
  assume ostth2.5: |- ( ph -> M e. ( ZZ>= ` 2 ) )
  assume ostth2.6: |- S = ( ( log ` ( F ` M ) ) / ( log ` M ) )
  assume ostth2.7: |- T = if ( ( F ` M ) <_ 1 , 1 , ( F ` M ) )
  assume ostth2.8: |- U = ( ( log ` N ) / ( log ` M ) )

  disjoint M x
  disjoint q x
  disjoint ph q
  disjoint ph x
  disjoint T x
  disjoint U x
  disjoint X x
  disjoint A q
  disjoint A x
  disjoint N x
  disjoint Q x
  disjoint F q
  disjoint R q
  disjoint F x
  disjoint k n
  disjoint k p
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint n p
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint p y
  disjoint p z
  disjoint G p
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint K k
  disjoint K n
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint M j
  disjoint k x
  disjoint M k
  disjoint n x
  disjoint M n
  disjoint a b
  disjoint a k
  disjoint a n
  disjoint a p
  disjoint a q
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint b k
  disjoint b n
  disjoint b p
  disjoint b q
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b ph
  disjoint k q
  disjoint k ph
  disjoint n q
  disjoint n ph
  disjoint p q
  disjoint p x
  disjoint p ph
  disjoint q y
  disjoint q z
  disjoint x y
  disjoint x z
  disjoint ph y
  disjoint ph z
  disjoint a g
  disjoint J a
  disjoint g p
  disjoint g y
  disjoint g z
  disjoint J g
  disjoint J p
  disjoint J y
  disjoint J z
  disjoint S a
  disjoint S b
  disjoint S k
  disjoint T j
  disjoint T k
  disjoint T n
  disjoint U n
  disjoint X k
  disjoint A a
  disjoint A k
  disjoint A n
  disjoint A p
  disjoint A y
  disjoint A z
  disjoint N k
  disjoint N n
  disjoint N y
  disjoint N z
  disjoint Q k
  disjoint Q n
  disjoint Q y
  disjoint Q z
  disjoint Y k
  disjoint a j
  disjoint F a
  disjoint b g
  disjoint b j
  disjoint F b
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint g q
  disjoint F g
  disjoint j p
  disjoint j q
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint F p
  disjoint F y
  disjoint F z
  disjoint P a
  disjoint P b
  disjoint P k
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint R a
  disjoint R p
  disjoint R y
  disjoint R z
  assert |- ( ( ph /\ X e. NN ) -> ( ( ( F ` N ) / ( T ^c U ) ) ^ X ) <_ ( X x. ( ( M x. T ) x. ( U + 1 ) ) ) )

  proof
    wph
    cX
    cn
    wcel
    #
    wa
    #
    cN
    cF
    cfv
    #
    cT
    cU
    ccxp
    co
    #
    cdiv
    co
    cX
    cexp
    co
    @2
    cX
    cexp
    co
    #
    @3
    cX
    cexp
    co
    #
    cdiv
    co
    #
    cX
    cM
    cT
    cmul
    co
    #
    cU
    c1
    caddc
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    cle
    @1
    @2
    @3
    cX
    @1
    @2
    wph
    @2
    cr
    wcel
    #
    @0
    wph
    cF
    cA
    wcel
    #
    cN
    cq
    wcel
    #
    @11
    ostth.1
    wph
    cN
    cn
    wcel
    #
    @13
    wph
    @14
    c1
    cN
    clt
    wbr
    #
    wph
    cN
    c2
    cuz
    cfv
    #
    wcel
    @14
    @15
    wa
    ostth2.2
    cN
    eluz2b2
    sylib
    #
    simpld
    #
    cN
    nnq
    syl
    #
    cA
    cq
    cQ
    cF
    cN
    qabsabv.a
    cQ
    qrng.q
    qrngbas
    #
    abvcl
    syl2anc
    #
    adantr
    recnd
    @1
    @3
    @1
    cT
    cU
    wph
    cT
    cr
    wcel
    #
    @0
    wph
    cT
    cM
    cF
    cfv
    #
    c1
    cle
    wbr
    #
    c1
    @23
    cif
    #
    cr
    ostth2.7
    wph
    c1
    cr
    wcel
    #
    @23
    cr
    wcel
    #
    @25
    cr
    wcel
    1re
    wph
    @12
    cM
    cq
    wcel
    #
    @27
    ostth.1
    wph
    cM
    cn
    wcel
    #
    @28
    wph
    @29
    c1
    cM
    clt
    wbr
    #
    wph
    cM
    @16
    wcel
    @29
    @30
    wa
    ostth2.5
    cM
    eluz2b2
    sylib
    #
    simpld
    #
    cM
    nnq
    syl
    cA
    cq
    cQ
    cF
    cM
    qabsabv.a
    @20
    abvcl
    syl2anc
    #
    @24
    c1
    @23
    cr
    ifcl
    sylancr
    syl5eqel
    #
    adantr
    #
    @1
    cT
    @1
    cT
    @35
    wph
    cc0
    cT
    clt
    wbr
    #
    @0
    wph
    cc0
    c1
    cT
    wph
    0red
    wph
    1red
    #
    @34
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    wph
    c1
    @25
    cT
    cle
    wph
    @27
    @26
    c1
    @25
    cle
    wbr
    @33
    @37
    @23
    c1
    max2
    syl2anc
    ostth2.7
    syl6breqr
    #
    ltletrd
    adantr
    #
    elrpd
    #
    rpge0d
    wph
    cU
    cr
    wcel
    #
    @0
    wph
    cU
    wph
    cU
    cN
    clog
    cfv
    #
    cM
    clog
    cfv
    #
    cdiv
    co
    #
    crp
    ostth2.8
    wph
    @42
    @43
    wph
    cN
    wph
    cN
    @18
    nnred
    wph
    @14
    @15
    @17
    simprd
    rplogcld
    #
    wph
    cM
    wph
    cM
    @32
    nnred
    wph
    @29
    @30
    @31
    simprd
    rplogcld
    #
    rpdivcld
    syl5eqel
    #
    rpred
    #
    adantr
    #
    recxpcld
    #
    recnd
    #
    @1
    @3
    @1
    cT
    cU
    @40
    @49
    rpcxpcld
    #
    rpne0d
    @0
    cX
    cn0
    wcel
    #
    wph
    cX
    nnnn0
    #
    adantl
    #
    expdivd
    @1
    @6
    @10
    cle
    wbr
    @4
    @5
    @10
    cmul
    co
    #
    cle
    wbr
    @1
    @4
    cM
    cX
    @8
    cmul
    co
    #
    cmul
    co
    #
    @5
    cT
    cmul
    co
    #
    cmul
    co
    #
    @56
    cle
    @1
    @4
    cM
    cX
    cU
    cmul
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cmul
    co
    #
    cT
    @63
    cexp
    co
    #
    cmul
    co
    #
    @60
    wph
    @11
    @53
    @4
    cr
    wcel
    @0
    @21
    @54
    @2
    cX
    reexpcl
    syl2an
    #
    @1
    @64
    @65
    @1
    cM
    @63
    @1
    cM
    wph
    @29
    @0
    @32
    adantr
    #
    nnred
    #
    @1
    @63
    @1
    @62
    cn0
    wcel
    #
    @63
    cn0
    wcel
    #
    @1
    @61
    cr
    wcel
    #
    cc0
    @61
    cle
    wbr
    @70
    @1
    cX
    cU
    @0
    cX
    cr
    wcel
    #
    wph
    cX
    nnre
    #
    adantl
    #
    @49
    remulcld
    #
    @1
    cX
    cU
    @75
    @49
    @1
    cX
    @55
    nn0ge0d
    wph
    cc0
    cU
    cle
    wbr
    @0
    wph
    cU
    @47
    rpge0d
    adantr
    mulge0d
    @61
    flge0nn0
    syl2anc
    #
    @62
    peano2nn0
    syl
    #
    nn0red
    #
    remulcld
    #
    @1
    cT
    @63
    @35
    @78
    reexpcld
    #
    remulcld
    #
    @1
    @58
    @59
    @1
    cM
    @57
    @69
    @1
    cX
    @8
    @75
    @1
    @41
    @8
    cr
    wcel
    @49
    cU
    peano2re
    syl
    #
    remulcld
    #
    remulcld
    #
    @1
    @5
    cT
    @1
    @3
    cX
    @50
    @55
    reexpcld
    #
    @35
    remulcld
    #
    remulcld
    #
    @1
    cN
    cX
    cexp
    co
    #
    cF
    cfv
    #
    @4
    @66
    cle
    @1
    @12
    @13
    @53
    @90
    @4
    wceq
    wph
    @12
    @0
    ostth.1
    adantr
    wph
    @13
    @0
    @19
    adantr
    @55
    cA
    cQ
    cF
    cN
    cX
    qrng.q
    qabsabv.a
    qabvexp
    syl3anc
    @1
    @89
    cc0
    cM
    @63
    cexp
    co
    #
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    @90
    @66
    cle
    wbr
    #
    @1
    @93
    @89
    @92
    cle
    wbr
    #
    @1
    @89
    @91
    clt
    wbr
    #
    @95
    @1
    cX
    @42
    cmul
    co
    #
    ce
    cfv
    #
    @63
    @43
    cmul
    co
    #
    ce
    cfv
    #
    @89
    @91
    clt
    @1
    @97
    @99
    clt
    wbr
    #
    @98
    @100
    clt
    wbr
    #
    @1
    @61
    @43
    cmul
    co
    #
    @97
    @99
    clt
    @1
    @97
    @43
    cdiv
    co
    #
    @43
    cmul
    co
    @103
    @97
    @1
    @104
    @61
    @43
    cmul
    @1
    @104
    cX
    @44
    cmul
    co
    @61
    @1
    cX
    @42
    @43
    @1
    cX
    @75
    recnd
    #
    wph
    @42
    cc
    wcel
    @0
    wph
    @42
    wph
    @42
    @45
    rpred
    #
    recnd
    adantr
    #
    wph
    @43
    cc
    wcel
    @0
    wph
    @43
    wph
    @43
    @46
    rpred
    #
    recnd
    adantr
    #
    @1
    @43
    wph
    @43
    crp
    wcel
    @0
    @46
    adantr
    #
    rpne0d
    #
    divassd
    cU
    @44
    cX
    cmul
    ostth2.8
    oveq2i
    syl6eqr
    oveq1d
    @1
    @97
    @43
    @1
    cX
    @42
    @105
    @107
    mulcld
    @109
    @111
    divcan1d
    eqtr3d
    @1
    @61
    @63
    @43
    @76
    @79
    @110
    @1
    @72
    @61
    @63
    clt
    wbr
    @76
    @61
    flltp1
    syl
    ltmul1dd
    eqbrtrrd
    @1
    @97
    cr
    wcel
    @99
    cr
    wcel
    @101
    @102
    wb
    @1
    cX
    @42
    @75
    wph
    @42
    cr
    wcel
    @0
    @106
    adantr
    remulcld
    @1
    @63
    @43
    @79
    wph
    @43
    cr
    wcel
    @0
    @108
    adantr
    remulcld
    @97
    @99
    eflt
    syl2anc
    mpbid
    wph
    cN
    crp
    wcel
    cX
    cz
    wcel
    #
    @89
    @98
    wceq
    @0
    wph
    cN
    @18
    nnrpd
    cX
    nnz
    #
    cN
    cX
    reexplog
    syl2an
    @1
    cM
    crp
    wcel
    @63
    cz
    wcel
    #
    @91
    @100
    wceq
    @1
    cM
    @68
    nnrpd
    @1
    @63
    @78
    nn0zd
    #
    cM
    @63
    reexplog
    syl2anc
    3brtr4d
    @1
    @89
    cn
    wcel
    #
    @91
    cn
    wcel
    @96
    @95
    wb
    wph
    @14
    @53
    @116
    @0
    @18
    @54
    cN
    cX
    nnexpcl
    syl2an
    #
    @1
    cM
    @63
    @68
    @78
    nnexpcld
    #
    @89
    @91
    nnltlem1
    syl2anc
    mpbid
    @1
    @89
    cc0
    cuz
    cfv
    #
    wcel
    @92
    cz
    wcel
    #
    @93
    @95
    wb
    @1
    @89
    cn0
    @119
    @1
    @89
    @117
    nnnn0d
    nn0uz
    syl6eleq
    @1
    @91
    cz
    wcel
    @120
    @1
    @91
    @118
    nnzd
    @91
    peano2zm
    syl
    @89
    cc0
    @92
    elfz5
    syl2anc
    mpbird
    wph
    @0
    @71
    @93
    @94
    wi
    @78
    wph
    @71
    @93
    @94
    wph
    vx
    cA
    cQ
    cR
    cS
    cT
    cF
    cJ
    cK
    cM
    cN
    @63
    @89
    vq
    qrng.q
    qabsabv.a
    padic.j
    ostth.k
    ostth.1
    ostth2.2
    ostth2.3
    ostth2.4
    ostth2.5
    ostth2.6
    ostth2.7
    ostth2lem2
    3expia
    syldan
    mpd
    eqbrtrrd
    @1
    @66
    @58
    @65
    cmul
    co
    #
    @60
    @82
    @1
    @58
    @65
    @85
    @81
    remulcld
    @88
    @1
    @64
    @58
    cle
    wbr
    #
    @66
    @121
    cle
    wbr
    #
    @1
    @63
    @57
    cle
    wbr
    #
    @122
    @1
    @63
    @61
    c1
    caddc
    co
    #
    @57
    @79
    @1
    @72
    @125
    cr
    wcel
    @76
    @61
    peano2re
    syl
    @84
    @1
    @62
    @61
    c1
    @1
    @62
    @77
    nn0red
    #
    @76
    @1
    1red
    #
    @1
    @72
    @62
    @61
    cle
    wbr
    @76
    @61
    flle
    syl
    #
    leadd1dd
    @1
    @125
    @61
    cX
    caddc
    co
    #
    @57
    cle
    @1
    c1
    cX
    @61
    @127
    @75
    @76
    @0
    c1
    cX
    cle
    wbr
    wph
    cX
    nnge1
    adantl
    leadd2dd
    @1
    @57
    @61
    cX
    c1
    cmul
    co
    #
    caddc
    co
    @129
    @1
    cX
    cU
    c1
    @105
    @1
    cU
    @49
    recnd
    #
    @1
    c1
    @127
    recnd
    adddid
    @1
    @130
    cX
    @61
    caddc
    @1
    cX
    @105
    mulid1d
    oveq2d
    eqtrd
    breqtrrd
    letrd
    @1
    @63
    cr
    wcel
    @57
    cr
    wcel
    cM
    cr
    wcel
    cc0
    cM
    clt
    wbr
    @124
    @122
    wb
    @79
    @84
    @69
    @1
    cM
    @68
    nngt0d
    #
    @63
    @57
    cM
    lemul2
    syl112anc
    mpbid
    @1
    @64
    cr
    wcel
    @58
    cr
    wcel
    #
    @65
    cr
    wcel
    #
    cc0
    @65
    clt
    wbr
    #
    @122
    @123
    wb
    @80
    @85
    @81
    @1
    @22
    @114
    @36
    @135
    @35
    @115
    @39
    cT
    @63
    expgt0
    syl3anc
    @64
    @58
    @65
    lemul1
    syl112anc
    mpbid
    @1
    @65
    @59
    cle
    wbr
    #
    @121
    @60
    cle
    wbr
    #
    @1
    @65
    cT
    @62
    cexp
    co
    #
    cT
    cmul
    co
    #
    @59
    cle
    @1
    cT
    @62
    @1
    cT
    @35
    recnd
    #
    @77
    expp1d
    @1
    @138
    @5
    cle
    wbr
    @139
    @59
    cle
    wbr
    @1
    cT
    @62
    ccxp
    co
    #
    cT
    cU
    cX
    cmul
    co
    #
    ccxp
    co
    #
    @138
    @5
    cle
    @1
    cT
    @62
    @142
    @35
    wph
    c1
    cT
    cle
    wbr
    @0
    @38
    adantr
    @126
    wph
    @41
    @73
    @142
    cr
    wcel
    @0
    @48
    @74
    cU
    cX
    remulcl
    syl2an
    @1
    @62
    @61
    @142
    cle
    @128
    @1
    cX
    cU
    @105
    @131
    mulcomd
    breqtrd
    cxplead
    @1
    cT
    cc
    wcel
    @70
    @141
    @138
    wceq
    @140
    @77
    cT
    @62
    cxpexp
    syl2anc
    @1
    @143
    @3
    cX
    ccxp
    co
    #
    @5
    @1
    cT
    cU
    cX
    @40
    @49
    @105
    cxpmuld
    @1
    @3
    cc
    wcel
    @53
    @144
    @5
    wceq
    @51
    @55
    @3
    cX
    cxpexp
    syl2anc
    eqtrd
    3brtr3d
    @1
    @138
    @5
    cT
    @1
    cT
    @62
    @35
    @77
    reexpcld
    @86
    @40
    lemul1d
    mpbid
    eqbrtrd
    @1
    @134
    @59
    cr
    wcel
    @133
    cc0
    @58
    clt
    wbr
    @136
    @137
    wb
    @81
    @87
    @85
    @1
    cM
    @57
    @69
    @84
    @132
    @1
    cX
    @8
    @75
    @83
    @0
    cc0
    cX
    clt
    wbr
    wph
    cX
    nngt0
    adantl
    @1
    cc0
    cU
    @8
    @1
    0red
    @49
    @83
    @1
    cU
    wph
    cU
    crp
    wcel
    @0
    @47
    adantr
    rpgt0d
    @1
    cU
    @49
    ltp1d
    lttrd
    mulgt0d
    mulgt0d
    @65
    @59
    @58
    lemul2
    syl112anc
    mpbid
    letrd
    letrd
    @1
    @60
    @5
    @58
    cT
    cmul
    co
    #
    cmul
    co
    @56
    @1
    @58
    @5
    cT
    @1
    @58
    @85
    recnd
    @1
    @5
    @86
    recnd
    @140
    mul12d
    @1
    @145
    @10
    @5
    cmul
    @1
    @145
    @7
    @57
    cmul
    co
    @10
    @1
    cM
    @57
    cT
    @1
    cM
    @69
    recnd
    #
    @1
    @57
    @84
    recnd
    @140
    mul32d
    @1
    @7
    cX
    @8
    @1
    cM
    cT
    @146
    @140
    mulcld
    @105
    @1
    @8
    @83
    recnd
    mul12d
    eqtrd
    oveq2d
    eqtrd
    breqtrd
    @1
    @4
    @10
    @5
    @67
    @1
    cX
    @9
    @75
    @1
    @7
    @8
    @1
    cM
    cT
    @69
    @35
    remulcld
    @83
    remulcld
    remulcld
    @1
    @3
    cX
    @52
    @0
    @112
    wph
    @113
    adantl
    rpexpcld
    ledivmuld
    mpbird
    eqbrtrd
end
