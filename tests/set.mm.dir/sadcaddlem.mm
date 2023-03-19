include "wcel.mm"
include "c0.mm"
include "cfv.mm"
include "wcad.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "cc0.mm"
include "cfzo.mm"
include "cin.mm"
include "cif.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wb.mm"
include "wa.mm"
include "wo.mm"
include "cad1.mm"
include "adantl.mm"
include "cr.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "nnexpcld.mm"
include "nnred.mm"
include "ad2antrr.mm"
include "cn0.mm"
include "cpw.mm"
include "cfn.mm"
include "wss.mm"
include "inss1.mm"
include "syl5ss.mm"
include "fzofi.mm"
include "inss2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "elfpw.mm"
include "sylanbrc.mm"
include "wf1o.mm"
include "wf.mm"
include "cbits.mm"
include "cres.mm"
include "ccnv.mm"
include "bitsf1o.mm"
include "f1ocnv.mm"
include "ax-mp.mm"
include "wceq.mm"
include "f1oeq1.mm"
include "mpbir.mm"
include "f1of.mm"
include "ffvelrni.mm"
include "syl.mm"
include "nn0addcld.mm"
include "nn0red.mm"
include "2nn0.mm"
include "adantr.mm"
include "nn0expcld.mm"
include "wn.mm"
include "0nn0.mm"
include "ifclda.mm"
include "biimpa.mm"
include "nnnn0d.mm"
include "ifcl.mm"
include "nn0ge0d.mm"
include "0red.mm"
include "addge01d.mm"
include "mpbid.mm"
include "iftrue.mm"
include "oveq1d.mm"
include "breqtrrd.mm"
include "addge02d.mm"
include "oveq2d.mm"
include "jaodan.mm"
include "le2addd.mm"
include "ex.mm"
include "ioran.mm"
include "clt.mm"
include "iffalse.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "oveq12d.mm"
include "00id.mm"
include "syl6eq.mm"
include "readdcld.mm"
include "recnd.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "fveq1i.mm"
include "fveq2i.mm"
include "fvres.mm"
include "f1ocnvfv2.mm"
include "sylancr.mm"
include "3eqtr3a.mm"
include "syl6eqss.mm"
include "cz.mm"
include "nn0zd.mm"
include "bitsfzo.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "elfzolt2.mm"
include "lt2addd.mm"
include "eqbrtrd.mm"
include "ltnled.mm"
include "syl5bi.mm"
include "impcon4bid.mm"
include "bitrd.mm"
include "cad0.mm"
include "oveqan12d.mm"
include "lenltd.mm"
include "con2bid.mm"
include "biimpar.mm"
include "ltadd1dd.mm"
include "wi.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "ltadd2d.mm"
include "sylibrd.mm"
include "nn0cnd.mm"
include "addid2d.mm"
include "leidd.mm"
include "breq1.mm"
include "ifboth.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "con1d.mm"
include "jcad.mm"
include "sylbid.mm"
include "syld.mm"
include "impbid.mm"
include "pm2.61dan.mm"
include "sadcp1.mm"
include "cmul.mm"
include "2cnd.mm"
include "expp1d.mm"
include "nncnd.mm"
include "times2d.mm"
include "bitsinvp1.mm"
include "add4d.mm"
include "breq12d.mm"
include "3bitr4d.mm"

theorem sadcaddlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let cK: class K
  let cN: class N
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume sadval.a: |- ( ph -> A C_ NN0 )
  assume sadval.b: |- ( ph -> B C_ NN0 )
  assume sadval.c: |- C = seq 0 ( ( c e. 2o , m e. NN0 |-> if ( cadd ( m e. A , m e. B , (/) e. c ) , 1o , (/) ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )
  assume sadcp1.n: |- ( ph -> N e. NN0 )
  assume sadcadd.k: |- K = `' ( bits |` NN0 )
  assume sadcaddlem.1: |- ( ph -> ( (/) e. ( C ` N ) <-> ( 2 ^ N ) <_ ( ( K ` ( A i^i ( 0 ..^ N ) ) ) + ( K ` ( B i^i ( 0 ..^ N ) ) ) ) ) )

  disjoint c m
  disjoint c n
  disjoint m n
  disjoint A c
  disjoint A m
  disjoint B c
  disjoint B m
  disjoint N n
  disjoint c k
  disjoint c x
  disjoint c y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A k
  disjoint A x
  disjoint A y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint C k
  disjoint C x
  disjoint C y
  disjoint K k
  disjoint K x
  disjoint k ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( (/) e. ( C ` ( N + 1 ) ) <-> ( 2 ^ ( N + 1 ) ) <_ ( ( K ` ( A i^i ( 0 ..^ ( N + 1 ) ) ) ) + ( K ` ( B i^i ( 0 ..^ ( N + 1 ) ) ) ) ) ) )

  proof
    wph
    cN
    cA
    wcel
    #
    cN
    cB
    wcel
    #
    c0
    cN
    cC
    cfv
    wcel
    #
    wcad
    #
    c2
    cN
    cexp
    co
    #
    @4
    caddc
    co
    #
    cA
    cc0
    cN
    cfzo
    co
    #
    cin
    #
    cK
    cfv
    #
    cB
    @6
    cin
    #
    cK
    cfv
    #
    caddc
    co
    #
    @0
    @4
    cc0
    cif
    #
    @1
    @4
    cc0
    cif
    #
    caddc
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    c0
    cN
    c1
    caddc
    co
    #
    cC
    cfv
    wcel
    c2
    @17
    cexp
    co
    #
    cA
    cc0
    @17
    cfzo
    co
    #
    cin
    cK
    cfv
    #
    cB
    @19
    cin
    cK
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    wph
    @2
    @3
    @16
    wb
    wph
    @2
    wa
    #
    @3
    @0
    @1
    wo
    #
    @16
    @2
    @3
    @24
    wb
    wph
    @0
    @1
    @2
    cad1
    adantl
    @23
    @24
    @16
    @23
    @24
    @16
    @23
    @24
    wa
    @4
    @4
    @11
    @14
    wph
    @4
    cr
    wcel
    #
    @2
    @24
    wph
    @4
    wph
    c2
    cN
    c2
    cn
    wcel
    wph
    2nn
    a1i
    sadcp1.n
    nnexpcld
    #
    nnred
    #
    ad2antrr
    #
    @28
    wph
    @11
    cr
    wcel
    #
    @2
    @24
    wph
    @11
    wph
    @8
    @10
    wph
    @7
    cn0
    cpw
    cfn
    cin
    #
    wcel
    #
    @8
    cn0
    wcel
    #
    wph
    @7
    cn0
    wss
    @7
    cfn
    wcel
    #
    @31
    wph
    @7
    cA
    cn0
    cA
    @6
    inss1
    sadval.a
    syl5ss
    wph
    @6
    cfn
    wcel
    #
    @7
    @6
    wss
    @33
    @34
    wph
    cc0
    cN
    fzofi
    a1i
    #
    cA
    @6
    inss2
    #
    @6
    @7
    ssfi
    sylancl
    @7
    cn0
    elfpw
    sylanbrc
    #
    @30
    cn0
    @7
    cK
    @30
    cn0
    cK
    wf1o
    #
    @30
    cn0
    cK
    wf
    @38
    @30
    cn0
    cbits
    cn0
    cres
    #
    ccnv
    #
    wf1o
    #
    cn0
    @30
    @39
    wf1o
    #
    @41
    bitsf1o
    cn0
    @30
    @39
    f1ocnv
    ax-mp
    cK
    @40
    wceq
    @38
    @41
    wb
    sadcadd.k
    @30
    cn0
    cK
    @40
    f1oeq1
    ax-mp
    mpbir
    @30
    cn0
    cK
    f1of
    ax-mp
    #
    ffvelrni
    syl
    #
    wph
    @9
    @30
    wcel
    #
    @10
    cn0
    wcel
    #
    wph
    @9
    cn0
    wss
    @9
    cfn
    wcel
    #
    @45
    wph
    @9
    cB
    cn0
    cB
    @6
    inss1
    sadval.b
    syl5ss
    wph
    @34
    @9
    @6
    wss
    @47
    @35
    cB
    @6
    inss2
    #
    @6
    @9
    ssfi
    sylancl
    @9
    cn0
    elfpw
    sylanbrc
    #
    @30
    cn0
    @9
    cK
    @43
    ffvelrni
    syl
    #
    nn0addcld
    #
    nn0red
    #
    ad2antrr
    wph
    @14
    cr
    wcel
    #
    @2
    @24
    wph
    @14
    wph
    @12
    @13
    wph
    @0
    @4
    cc0
    cn0
    wph
    @0
    wa
    #
    c2
    cN
    c2
    cn0
    wcel
    #
    @54
    2nn0
    a1i
    wph
    cN
    cn0
    wcel
    #
    @0
    sadcp1.n
    adantr
    nn0expcld
    cc0
    cn0
    wcel
    #
    wph
    @0
    wn
    #
    wa
    #
    0nn0
    a1i
    ifclda
    wph
    @1
    @4
    cc0
    cn0
    wph
    @1
    wa
    #
    c2
    cN
    @55
    @60
    2nn0
    a1i
    wph
    @56
    @1
    sadcp1.n
    adantr
    nn0expcld
    @57
    wph
    @1
    wn
    #
    wa
    #
    0nn0
    a1i
    ifclda
    nn0addcld
    nn0red
    #
    ad2antrr
    @23
    @4
    @11
    cle
    wbr
    #
    @24
    wph
    @2
    @64
    sadcaddlem.1
    biimpa
    adantr
    @23
    @0
    @4
    @14
    cle
    wbr
    @1
    @23
    @0
    wa
    #
    @4
    @4
    @13
    caddc
    co
    #
    @14
    cle
    wph
    @4
    @66
    cle
    wbr
    #
    @2
    @0
    wph
    cc0
    @13
    cle
    wbr
    @67
    wph
    @13
    wph
    @4
    cn0
    wcel
    #
    @57
    @13
    cn0
    wcel
    wph
    @4
    @26
    nnnn0d
    #
    0nn0
    @1
    @4
    cc0
    cn0
    ifcl
    sylancl
    #
    nn0ge0d
    wph
    @4
    @13
    @27
    wph
    @1
    @4
    cc0
    cr
    wph
    @25
    @1
    @27
    adantr
    @62
    0red
    ifclda
    #
    addge01d
    mpbid
    ad2antrr
    @65
    @12
    @4
    @13
    caddc
    @0
    @12
    @4
    wceq
    @23
    @0
    @4
    cc0
    iftrue
    #
    adantl
    oveq1d
    breqtrrd
    @23
    @1
    wa
    #
    @4
    @12
    @4
    caddc
    co
    #
    @14
    cle
    wph
    @4
    @74
    cle
    wbr
    #
    @2
    @1
    wph
    cc0
    @12
    cle
    wbr
    @75
    wph
    @12
    wph
    @68
    @57
    @12
    cn0
    wcel
    @69
    0nn0
    @0
    @4
    cc0
    cn0
    ifcl
    sylancl
    #
    nn0ge0d
    wph
    @4
    @12
    @27
    wph
    @0
    @4
    cc0
    cr
    wph
    @25
    @0
    @27
    adantr
    @59
    0red
    ifclda
    #
    addge02d
    mpbid
    ad2antrr
    @73
    @13
    @4
    @12
    caddc
    @1
    @13
    @4
    wceq
    @23
    @1
    @4
    cc0
    iftrue
    #
    adantl
    oveq2d
    breqtrrd
    jaodan
    le2addd
    ex
    @24
    wn
    @58
    @61
    wa
    #
    @23
    @16
    wn
    #
    @0
    @1
    ioran
    @23
    @79
    @80
    @23
    @79
    wa
    #
    @15
    @5
    clt
    wbr
    @80
    @81
    @15
    @11
    @5
    clt
    @81
    @15
    @11
    cc0
    caddc
    co
    @11
    @81
    @14
    cc0
    @11
    caddc
    @81
    @14
    cc0
    cc0
    caddc
    co
    cc0
    @81
    @12
    cc0
    @13
    cc0
    caddc
    @58
    @12
    cc0
    wceq
    @23
    @61
    @0
    @4
    cc0
    iffalse
    #
    ad2antrl
    @61
    @13
    cc0
    wceq
    @23
    @58
    @1
    @4
    cc0
    iffalse
    #
    ad2antll
    oveq12d
    00id
    syl6eq
    oveq2d
    @81
    @11
    @81
    @11
    @81
    @8
    @10
    wph
    @8
    cr
    wcel
    #
    @2
    @79
    wph
    @8
    @44
    nn0red
    #
    ad2antrr
    wph
    @10
    cr
    wcel
    #
    @2
    @79
    wph
    @10
    @50
    nn0red
    #
    ad2antrr
    readdcld
    #
    recnd
    addid1d
    eqtrd
    wph
    @11
    @5
    clt
    wbr
    @2
    @79
    wph
    @8
    @10
    @4
    @4
    @85
    @87
    @27
    @27
    wph
    @8
    cc0
    @4
    cfzo
    co
    #
    wcel
    #
    @8
    @4
    clt
    wbr
    wph
    @90
    @8
    cbits
    cfv
    #
    @6
    wss
    #
    wph
    @91
    @7
    @6
    wph
    @8
    @39
    cfv
    #
    @7
    @40
    cfv
    #
    @39
    cfv
    #
    @91
    @7
    @8
    @94
    @39
    @7
    cK
    @40
    sadcadd.k
    fveq1i
    fveq2i
    wph
    @32
    @93
    @91
    wceq
    @44
    @8
    cn0
    cbits
    fvres
    syl
    wph
    @42
    @31
    @95
    @7
    wceq
    bitsf1o
    @37
    cn0
    @30
    @7
    @39
    f1ocnvfv2
    sylancr
    3eqtr3a
    @36
    syl6eqss
    wph
    @8
    cz
    wcel
    @56
    @90
    @92
    wb
    wph
    @8
    @44
    nn0zd
    sadcp1.n
    cN
    @8
    bitsfzo
    syl2anc
    mpbird
    @8
    cc0
    @4
    elfzolt2
    syl
    wph
    @10
    @89
    wcel
    #
    @10
    @4
    clt
    wbr
    wph
    @96
    @10
    cbits
    cfv
    #
    @6
    wss
    #
    wph
    @97
    @9
    @6
    wph
    @10
    @39
    cfv
    #
    @9
    @40
    cfv
    #
    @39
    cfv
    #
    @97
    @9
    @10
    @100
    @39
    @9
    cK
    @40
    sadcadd.k
    fveq1i
    fveq2i
    wph
    @46
    @99
    @97
    wceq
    @50
    @10
    cn0
    cbits
    fvres
    syl
    wph
    @42
    @45
    @101
    @9
    wceq
    bitsf1o
    @49
    cn0
    @30
    @9
    @39
    f1ocnvfv2
    sylancr
    3eqtr3a
    @48
    syl6eqss
    wph
    @10
    cz
    wcel
    @56
    @96
    @98
    wb
    wph
    @10
    @50
    nn0zd
    sadcp1.n
    cN
    @10
    bitsfzo
    syl2anc
    mpbird
    @10
    cc0
    @4
    elfzolt2
    syl
    lt2addd
    ad2antrr
    eqbrtrd
    @81
    @15
    @5
    @81
    @11
    @14
    @88
    @81
    @12
    @13
    wph
    @12
    cr
    wcel
    @2
    @79
    @77
    ad2antrr
    wph
    @13
    cr
    wcel
    @2
    @79
    @71
    ad2antrr
    readdcld
    readdcld
    @81
    @4
    @4
    wph
    @25
    @2
    @79
    @27
    ad2antrr
    #
    @102
    readdcld
    ltnled
    mpbid
    ex
    syl5bi
    impcon4bid
    bitrd
    wph
    @2
    wn
    #
    wa
    #
    @3
    @0
    @1
    wa
    #
    @16
    @103
    @3
    @105
    wb
    wph
    @0
    @1
    @2
    cad0
    adantl
    @104
    @105
    @16
    @104
    @105
    @16
    @104
    @105
    wa
    #
    @5
    @11
    @5
    caddc
    co
    #
    @15
    cle
    wph
    @5
    @107
    cle
    wbr
    #
    @103
    @105
    wph
    cc0
    @11
    cle
    wbr
    @108
    wph
    @11
    @51
    nn0ge0d
    wph
    @5
    @11
    wph
    @4
    @4
    @27
    @27
    readdcld
    #
    @52
    addge02d
    mpbid
    ad2antrr
    @106
    @14
    @5
    @11
    caddc
    @105
    @14
    @5
    wceq
    @104
    @0
    @1
    @12
    @4
    @13
    @4
    caddc
    @72
    @78
    oveqan12d
    adantl
    oveq2d
    breqtrrd
    ex
    @104
    @16
    @4
    @14
    clt
    wbr
    #
    @105
    @104
    @16
    @11
    @4
    caddc
    co
    #
    @15
    clt
    wbr
    #
    @110
    @104
    @111
    @5
    clt
    wbr
    #
    @16
    @112
    @104
    @11
    @4
    @4
    @104
    @8
    @10
    wph
    @84
    @103
    @85
    adantr
    wph
    @86
    @103
    @87
    adantr
    readdcld
    #
    wph
    @25
    @103
    @27
    adantr
    #
    @115
    wph
    @11
    @4
    clt
    wbr
    #
    @103
    wph
    @2
    @116
    wph
    @2
    @64
    @116
    wn
    sadcaddlem.1
    wph
    @4
    @11
    @27
    @52
    lenltd
    bitrd
    con2bid
    biimpar
    ltadd1dd
    @104
    @111
    cr
    wcel
    @5
    cr
    wcel
    #
    @15
    cr
    wcel
    #
    @113
    @16
    wa
    @112
    wi
    @104
    @11
    @4
    @114
    @115
    readdcld
    wph
    @117
    @103
    @109
    adantr
    wph
    @118
    @103
    wph
    @11
    @14
    @52
    @63
    readdcld
    adantr
    @111
    @5
    @15
    ltletr
    syl3anc
    mpand
    @104
    @4
    @14
    @11
    @115
    wph
    @53
    @103
    @63
    adantr
    wph
    @29
    @103
    @52
    adantr
    ltadd2d
    sylibrd
    wph
    @110
    @105
    wi
    @103
    wph
    @110
    @14
    @4
    cle
    wbr
    #
    wn
    #
    @105
    wph
    @4
    @14
    @27
    @63
    ltnled
    wph
    @120
    @0
    @1
    wph
    @0
    @119
    wph
    @119
    @58
    cc0
    @13
    caddc
    co
    #
    @4
    cle
    wbr
    wph
    @121
    @13
    @4
    cle
    wph
    @13
    wph
    @13
    @70
    nn0cnd
    #
    addid2d
    wph
    @4
    @4
    cle
    wbr
    #
    cc0
    @4
    cle
    wbr
    #
    @13
    @4
    cle
    wbr
    #
    wph
    @4
    @27
    leidd
    #
    wph
    @4
    @69
    nn0ge0d
    #
    @1
    @123
    @124
    @125
    @4
    cc0
    @4
    @13
    @4
    cle
    breq1
    cc0
    @13
    @4
    cle
    breq1
    ifboth
    syl2anc
    eqbrtrd
    @58
    @14
    @121
    @4
    cle
    @58
    @12
    cc0
    @13
    caddc
    @82
    oveq1d
    breq1d
    syl5ibrcom
    con1d
    wph
    @1
    @119
    wph
    @119
    @61
    @12
    cc0
    caddc
    co
    #
    @4
    cle
    wbr
    wph
    @128
    @12
    @4
    cle
    wph
    @12
    wph
    @12
    @76
    nn0cnd
    #
    addid1d
    wph
    @123
    @124
    @12
    @4
    cle
    wbr
    #
    @126
    @127
    @0
    @123
    @124
    @130
    @4
    cc0
    @4
    @12
    @4
    cle
    breq1
    cc0
    @12
    @4
    cle
    breq1
    ifboth
    syl2anc
    eqbrtrd
    @61
    @14
    @128
    @4
    cle
    @61
    @13
    cc0
    @12
    caddc
    @83
    oveq2d
    breq1d
    syl5ibrcom
    con1d
    jcad
    sylbid
    adantr
    syld
    impbid
    bitrd
    pm2.61dan
    wph
    cA
    cB
    cC
    vm
    vn
    cN
    vc
    sadval.a
    sadval.b
    sadval.c
    sadcp1.n
    sadcp1
    wph
    @18
    @5
    @22
    @15
    cle
    wph
    @18
    @4
    c2
    cmul
    co
    @5
    wph
    c2
    cN
    wph
    2cnd
    sadcp1.n
    expp1d
    wph
    @4
    wph
    @4
    @26
    nncnd
    times2d
    eqtrd
    wph
    @22
    @8
    @12
    caddc
    co
    #
    @10
    @13
    caddc
    co
    #
    caddc
    co
    @15
    wph
    @20
    @131
    @21
    @132
    caddc
    wph
    cA
    cn0
    wss
    @56
    @20
    @131
    wceq
    sadval.a
    sadcp1.n
    cA
    cK
    cN
    sadcadd.k
    bitsinvp1
    syl2anc
    wph
    cB
    cn0
    wss
    @56
    @21
    @132
    wceq
    sadval.b
    sadcp1.n
    cB
    cK
    cN
    sadcadd.k
    bitsinvp1
    syl2anc
    oveq12d
    wph
    @8
    @12
    @10
    @13
    wph
    @8
    @44
    nn0cnd
    @129
    wph
    @10
    @50
    nn0cnd
    @122
    add4d
    eqtrd
    breq12d
    3bitr4d
end
