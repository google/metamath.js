include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "ciun.mm"
include "chash.mm"
include "cprime.mm"
include "cdiv.mm"
include "cc0.mm"
include "cif.mm"
include "csu.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wceq.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "fveq2d.mm"
include "sumeq1d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cz.mm"
include "0le0.mm"
include "nncnd.mm"
include "mul01d.mm"
include "syl5breqr.mm"
include "c0.mm"
include "clt.mm"
include "nnred.mm"
include "ltp1d.mm"
include "wb.mm"
include "nnzd.mm"
include "peano2zd.mm"
include "fzn.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "0iun.mm"
include "syl6eq.mm"
include "hash0.mm"
include "sum0.mm"
include "3brtr4d.mm"
include "a1i.mm"
include "wa.mm"
include "cfn.mm"
include "cn0.mm"
include "wss.mm"
include "fzfi.mm"
include "wral.mm"
include "elfzuz.mm"
include "cn.mm"
include "peano2nnd.mm"
include "eluznn.mm"
include "sylan.mm"
include "cdvds.mm"
include "crab.mm"
include "eleq1.mm"
include "breq1.mm"
include "anbi12d.mm"
include "rabbidv.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "syldan.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "iunss.mm"
include "sylibr.mm"
include "ssfi.mm"
include "sylancr.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0red.mm"
include "cr.mm"
include "fzfid.mm"
include "syl2an.mm"
include "nnrecre.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "fsumrecl.mm"
include "remulcld.mm"
include "prmnn.mm"
include "wn.mm"
include "0red.mm"
include "ifclda.mm"
include "leadd1d.mm"
include "cmin.mm"
include "eluzp1p1.mm"
include "cc.mm"
include "simpl.mm"
include "recnd.mm"
include "ifbieq1d.mm"
include "fsumm1.mm"
include "eluzelz.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "adddid.mm"
include "breq2d.mm"
include "bitr4d.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "readdcld.mm"
include "cun.mm"
include "csn.mm"
include "simpr.mm"
include "eleqtrrd.mm"
include "fzsuc2.mm"
include "iunxun.mm"
include "iunxsn.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "hashun2.mm"
include "eqbrtrd.mm"
include "cfl.mm"
include "nndivred.mm"
include "flle.mm"
include "elfznn.mm"
include "subid1d.mm"
include "rabbiia.mm"
include "fveq2i.mm"
include "1zzd.mm"
include "nnnn0d.mm"
include "nn0uz.mm"
include "1m1e0.mm"
include "eqtr4i.mm"
include "syl6eleq.mm"
include "0zd.mm"
include "hashdvds.mm"
include "oveq1i.mm"
include "0m0e0.mm"
include "nnne0d.mm"
include "div0d.mm"
include "syl5eq.mm"
include "0z.mm"
include "flid.mm"
include "ax-mp.mm"
include "oveq12d.mm"
include "flcld.mm"
include "3eqtrd.mm"
include "syl5eqr.mm"
include "divrecd.mm"
include "eqcomd.mm"
include "biantrurd.mm"
include "eqtr4d.mm"
include "iftrue.mm"
include "con3i.mm"
include "ralrimivw.mm"
include "rabeq0.mm"
include "sylan9eq.mm"
include "iffalse.mm"
include "sylan9eqr.mm"
include "pm2.61dan.mm"
include "leadd2dd.mm"
include "letrd.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "sylbid.mm"
include "expcom.mm"
include "a2d.mm"
include "uzind4.mm"
include "com12.mm"

theorem prmreclem4
  let wph: wff ph
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let cW: class W
  let vp: setvar p
  let vj: setvar j
  let vm: setvar m
  let vr: setvar r
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vq: setvar q
  let cA: class A
  let cQ: class Q
  assume prmrec.1: |- F = ( n e. NN |-> if ( n e. Prime , ( 1 / n ) , 0 ) )
  assume prmrec.2: |- ( ph -> K e. NN )
  assume prmrec.3: |- ( ph -> N e. NN )
  assume prmrec.4: |- M = { n e. ( 1 ... N ) | A. p e. ( Prime \ ( 1 ... K ) ) -. p || n }
  assume prmrec.5: |- ( ph -> seq 1 ( + , F ) e. dom ~~> )
  assume prmrec.6: |- ( ph -> sum_ k e. ( ZZ>= ` ( K + 1 ) ) if ( k e. Prime , ( 1 / k ) , 0 ) < ( 1 / 2 ) )
  assume prmrec.7: |- W = ( p e. NN |-> { n e. ( 1 ... N ) | ( p e. Prime /\ p || n ) } )

  disjoint k n
  disjoint k p
  disjoint F k
  disjoint n p
  disjoint F n
  disjoint F p
  disjoint K k
  disjoint K n
  disjoint K p
  disjoint M k
  disjoint M n
  disjoint M p
  disjoint k ph
  disjoint n ph
  disjoint p ph
  disjoint W k
  disjoint N k
  disjoint N n
  disjoint N p
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j p
  disjoint j r
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k r
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m p
  disjoint m r
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n r
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p r
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint j q
  disjoint K j
  disjoint k q
  disjoint n q
  disjoint p q
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint K q
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint M q
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint A r
  disjoint j ph
  disjoint ph q
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint Q n
  disjoint Q p
  disjoint Q r
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint W j
  disjoint W q
  disjoint W x
  disjoint N j
  disjoint N q
  disjoint N x
  disjoint N y
  disjoint N z
  assert |- ( ph -> ( N e. ( ZZ>= ` K ) -> ( # ` U_ k e. ( ( K + 1 ) ... N ) ( W ` k ) ) <_ ( N x. sum_ k e. ( ( K + 1 ) ... N ) if ( k e. Prime , ( 1 / k ) , 0 ) ) ) )

  proof
    cN
    cK
    cuz
    cfv
    #
    wcel
    wph
    vk
    cK
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    vk
    cv
    #
    cW
    cfv
    #
    ciun
    #
    chash
    cfv
    #
    cN
    @2
    @3
    cprime
    wcel
    #
    c1
    @3
    cdiv
    co
    #
    cc0
    cif
    #
    vk
    csu
    #
    cmul
    co
    #
    cle
    wbr
    #
    wph
    vk
    @1
    vx
    cv
    #
    cfz
    co
    #
    @4
    ciun
    #
    chash
    cfv
    #
    cN
    @14
    @9
    vk
    csu
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    wph
    vk
    @1
    cK
    cfz
    co
    #
    @4
    ciun
    #
    chash
    cfv
    #
    cN
    @20
    @9
    vk
    csu
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    #
    wph
    vk
    @1
    vj
    cv
    #
    cfz
    co
    #
    @4
    ciun
    #
    chash
    cfv
    #
    cN
    @28
    @9
    vk
    csu
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    wph
    vk
    @1
    @27
    c1
    caddc
    co
    #
    cfz
    co
    #
    @4
    ciun
    #
    chash
    cfv
    #
    cN
    @35
    @9
    vk
    csu
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    wph
    @12
    wi
    vx
    vj
    cK
    cN
    @13
    cK
    wceq
    #
    @19
    @25
    wph
    @41
    @16
    @22
    @18
    @24
    cle
    @41
    @15
    @21
    chash
    @41
    vk
    @14
    @20
    @4
    @13
    cK
    @1
    cfz
    oveq2
    #
    iuneq1d
    fveq2d
    @41
    @17
    @23
    cN
    cmul
    @41
    @14
    @20
    @9
    vk
    @42
    sumeq1d
    oveq2d
    breq12d
    imbi2d
    vx
    vj
    weq
    #
    @19
    @33
    wph
    @43
    @16
    @30
    @18
    @32
    cle
    @43
    @15
    @29
    chash
    @43
    vk
    @14
    @28
    @4
    @13
    @27
    @1
    cfz
    oveq2
    #
    iuneq1d
    fveq2d
    @43
    @17
    @31
    cN
    cmul
    @43
    @14
    @28
    @9
    vk
    @44
    sumeq1d
    oveq2d
    breq12d
    imbi2d
    @13
    @34
    wceq
    #
    @19
    @40
    wph
    @45
    @16
    @37
    @18
    @39
    cle
    @45
    @15
    @36
    chash
    @45
    vk
    @14
    @35
    @4
    @13
    @34
    @1
    cfz
    oveq2
    #
    iuneq1d
    fveq2d
    @45
    @17
    @38
    cN
    cmul
    @45
    @14
    @35
    @9
    vk
    @46
    sumeq1d
    oveq2d
    breq12d
    imbi2d
    @13
    cN
    wceq
    #
    @19
    @12
    wph
    @47
    @16
    @6
    @18
    @11
    cle
    @47
    @15
    @5
    chash
    @47
    vk
    @14
    @2
    @4
    @13
    cN
    @1
    cfz
    oveq2
    #
    iuneq1d
    fveq2d
    @47
    @17
    @10
    cN
    cmul
    @47
    @14
    @2
    @9
    vk
    @48
    sumeq1d
    oveq2d
    breq12d
    imbi2d
    @26
    cK
    cz
    wcel
    #
    wph
    cc0
    cN
    cc0
    cmul
    co
    #
    @22
    @24
    cle
    wph
    cc0
    cc0
    @50
    cle
    0le0
    wph
    cN
    wph
    cN
    prmrec.3
    nncnd
    #
    mul01d
    #
    syl5breqr
    wph
    @22
    c0
    chash
    cfv
    #
    cc0
    wph
    @21
    c0
    chash
    wph
    @21
    vk
    c0
    @4
    ciun
    c0
    wph
    vk
    @20
    c0
    @4
    wph
    cK
    @1
    clt
    wbr
    #
    @20
    c0
    wceq
    #
    wph
    cK
    wph
    cK
    prmrec.2
    nnred
    ltp1d
    wph
    @1
    cz
    wcel
    #
    @49
    @54
    @55
    wb
    wph
    cK
    wph
    cK
    prmrec.2
    nnzd
    #
    peano2zd
    #
    @57
    @1
    cK
    fzn
    syl2anc
    mpbid
    #
    iuneq1d
    vk
    @4
    0iun
    syl6eq
    fveq2d
    hash0
    syl6eq
    wph
    @23
    cc0
    cN
    cmul
    wph
    @23
    c0
    @9
    vk
    csu
    cc0
    wph
    @20
    c0
    @9
    vk
    @59
    sumeq1d
    @9
    vk
    sum0
    syl6eq
    oveq2d
    3brtr4d
    a1i
    @27
    @0
    wcel
    #
    wph
    @33
    @40
    wph
    @60
    @33
    @40
    wi
    wph
    @60
    wa
    #
    @33
    @30
    cN
    @34
    cprime
    wcel
    #
    c1
    @34
    cdiv
    co
    #
    cc0
    cif
    #
    cmul
    co
    #
    caddc
    co
    #
    @39
    cle
    wbr
    #
    @40
    @61
    @33
    @66
    @32
    @65
    caddc
    co
    #
    cle
    wbr
    @67
    @61
    @30
    @32
    @65
    @61
    @30
    @61
    @29
    cfn
    wcel
    #
    @30
    cn0
    wcel
    @61
    c1
    cN
    cfz
    co
    #
    cfn
    wcel
    #
    @29
    @70
    wss
    #
    @69
    c1
    cN
    fzfi
    #
    @61
    @4
    @70
    wss
    #
    vk
    @28
    wral
    #
    @72
    wph
    @75
    @60
    wph
    @74
    vk
    @28
    @3
    @28
    wcel
    #
    wph
    @3
    @1
    cuz
    cfv
    #
    wcel
    #
    @74
    @3
    @1
    @27
    elfzuz
    #
    wph
    @78
    @3
    cn
    wcel
    #
    @74
    wph
    @1
    cn
    wcel
    #
    @78
    @80
    wph
    cK
    prmrec.2
    peano2nnd
    #
    @3
    @1
    eluznn
    #
    sylan
    #
    wph
    @80
    wa
    @4
    @7
    @3
    vn
    cv
    #
    cdvds
    wbr
    #
    wa
    #
    vn
    @70
    crab
    #
    @70
    @80
    @4
    @88
    wceq
    wph
    vp
    @3
    vp
    cv
    #
    cprime
    wcel
    #
    @89
    @85
    cdvds
    wbr
    #
    wa
    #
    vn
    @70
    crab
    #
    @88
    cn
    cW
    vp
    vk
    weq
    #
    @92
    @87
    vn
    @70
    @94
    @90
    @7
    @91
    @86
    @89
    @3
    cprime
    eleq1
    @89
    @3
    @85
    cdvds
    breq1
    anbi12d
    rabbidv
    prmrec.7
    @87
    vn
    @70
    c1
    cN
    cfz
    ovex
    #
    rabex
    fvmpt
    adantl
    @87
    vn
    @70
    ssrab2
    syl6eqss
    #
    syldan
    #
    sylan2
    ralrimiva
    adantr
    vk
    @28
    @4
    @70
    iunss
    sylibr
    @70
    @29
    ssfi
    sylancr
    #
    @29
    hashcl
    syl
    nn0red
    #
    @61
    cN
    @31
    wph
    cN
    cr
    wcel
    @60
    wph
    cN
    prmrec.3
    nnred
    adantr
    #
    @61
    @28
    @9
    vk
    @61
    @1
    @27
    fzfid
    @61
    @76
    wa
    @80
    @9
    cr
    wcel
    #
    @61
    @81
    @78
    @80
    @76
    wph
    @81
    @60
    @82
    adantr
    @79
    @83
    syl2an
    @80
    @8
    cr
    wcel
    cc0
    cr
    wcel
    @101
    @3
    nnrecre
    0re
    @7
    @8
    cc0
    cr
    ifcl
    sylancl
    #
    syl
    fsumrecl
    #
    remulcld
    @61
    cN
    @64
    @100
    @61
    @62
    @63
    cc0
    cr
    @62
    @63
    cr
    wcel
    #
    @61
    @62
    @34
    cn
    wcel
    #
    @104
    @34
    prmnn
    @34
    nnrecre
    syl
    adantl
    @61
    @62
    wn
    #
    wa
    #
    0red
    ifclda
    #
    remulcld
    #
    leadd1d
    @61
    @39
    @68
    @66
    cle
    @61
    @39
    cN
    @31
    @64
    caddc
    co
    #
    cmul
    co
    @68
    @61
    @38
    @110
    cN
    cmul
    @61
    @38
    @1
    @34
    c1
    cmin
    co
    #
    cfz
    co
    #
    @9
    vk
    csu
    #
    @64
    caddc
    co
    @110
    @61
    @9
    @64
    vk
    @1
    @34
    @60
    @34
    @77
    wcel
    wph
    cK
    @27
    eluzp1p1
    adantl
    @61
    wph
    @78
    @9
    cc
    wcel
    #
    @3
    @35
    wcel
    #
    wph
    @60
    simpl
    #
    @3
    @1
    @34
    elfzuz
    #
    wph
    @78
    wa
    #
    @80
    @114
    @84
    @80
    @9
    @102
    recnd
    syl
    syl2an
    @3
    @34
    wceq
    #
    @7
    @62
    @8
    @63
    cc0
    @3
    @34
    cprime
    eleq1
    @3
    @34
    c1
    cdiv
    oveq2
    ifbieq1d
    fsumm1
    @61
    @113
    @31
    @64
    caddc
    @61
    @112
    @28
    @9
    vk
    @61
    @111
    @27
    @1
    cfz
    @61
    @27
    cc
    wcel
    c1
    cc
    wcel
    #
    @111
    @27
    wceq
    @61
    @27
    @60
    @27
    cz
    wcel
    wph
    cK
    @27
    eluzelz
    adantl
    zcnd
    ax-1cn
    @27
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    oveq1d
    eqtrd
    oveq2d
    @61
    cN
    @31
    @64
    wph
    cN
    cc
    wcel
    @60
    @51
    adantr
    #
    @61
    @31
    @103
    recnd
    @61
    @64
    @108
    recnd
    adddid
    eqtrd
    breq2d
    bitr4d
    @61
    @37
    @66
    cle
    wbr
    #
    @67
    @40
    @61
    @37
    @30
    @34
    cW
    cfv
    #
    chash
    cfv
    #
    caddc
    co
    #
    @66
    @61
    @37
    @61
    @36
    cfn
    wcel
    #
    @37
    cn0
    wcel
    @61
    @71
    @36
    @70
    wss
    #
    @126
    @73
    @61
    @74
    vk
    @35
    wral
    #
    @127
    wph
    @128
    @60
    wph
    @74
    vk
    @35
    @115
    wph
    @78
    @74
    @117
    @97
    sylan2
    ralrimiva
    adantr
    vk
    @35
    @4
    @70
    iunss
    sylibr
    @70
    @36
    ssfi
    sylancr
    @36
    hashcl
    syl
    nn0red
    #
    @61
    @30
    @124
    @99
    @61
    @124
    @61
    @123
    cfn
    wcel
    #
    @124
    cn0
    wcel
    @61
    @71
    @123
    @70
    wss
    #
    @130
    @73
    @61
    @105
    @74
    vk
    cn
    wral
    #
    @131
    @61
    @27
    wph
    cK
    cn
    wcel
    @60
    @27
    cn
    wcel
    prmrec.2
    @27
    cK
    eluznn
    sylan
    peano2nnd
    #
    wph
    @132
    @60
    wph
    @74
    vk
    cn
    @96
    ralrimiva
    adantr
    @74
    @131
    vk
    @34
    cn
    @119
    @4
    @123
    @70
    @3
    @34
    cW
    fveq2
    #
    sseq1d
    rspcv
    sylc
    @70
    @123
    ssfi
    sylancr
    #
    @123
    hashcl
    syl
    nn0red
    #
    readdcld
    @61
    @30
    @65
    @99
    @109
    readdcld
    #
    @61
    @37
    @29
    @123
    cun
    #
    chash
    cfv
    #
    @125
    cle
    @61
    @36
    @138
    chash
    @61
    @36
    vk
    @28
    @34
    csn
    #
    cun
    #
    @4
    ciun
    #
    @138
    @61
    vk
    @35
    @141
    @4
    @61
    @56
    @27
    @1
    c1
    cmin
    co
    #
    cuz
    cfv
    #
    wcel
    @35
    @141
    wceq
    wph
    @56
    @60
    @58
    adantr
    @61
    @27
    @0
    @144
    wph
    @60
    simpr
    @61
    @143
    cK
    cuz
    @61
    cK
    cc
    wcel
    #
    @120
    @143
    cK
    wceq
    wph
    @145
    @60
    wph
    cK
    prmrec.2
    nncnd
    adantr
    ax-1cn
    cK
    c1
    pncan
    sylancl
    fveq2d
    eleqtrrd
    @1
    @27
    fzsuc2
    syl2anc
    iuneq1d
    @142
    @29
    vk
    @140
    @4
    ciun
    #
    cun
    @138
    vk
    @28
    @140
    @4
    iunxun
    @146
    @123
    @29
    vk
    @34
    @4
    @123
    @27
    c1
    caddc
    ovex
    @134
    iunxsn
    uneq2i
    eqtri
    syl6eq
    fveq2d
    @61
    @69
    @130
    @139
    @125
    cle
    wbr
    @98
    @135
    @29
    @123
    hashun2
    syl2anc
    eqbrtrd
    @61
    @124
    @65
    @30
    @136
    @109
    @99
    @61
    @62
    @124
    @65
    cle
    wbr
    @61
    @62
    wa
    #
    @34
    @85
    cdvds
    wbr
    #
    vn
    @70
    crab
    #
    chash
    cfv
    #
    cN
    @63
    cmul
    co
    #
    @124
    @65
    cle
    @61
    @150
    @151
    cle
    wbr
    @62
    @61
    cN
    @34
    cdiv
    co
    #
    cfl
    cfv
    #
    @152
    @150
    @151
    cle
    @61
    @152
    cr
    wcel
    @153
    @152
    cle
    wbr
    @61
    cN
    @34
    @100
    @133
    nndivred
    #
    @152
    flle
    syl
    @61
    @150
    @34
    @85
    cc0
    cmin
    co
    #
    cdvds
    wbr
    #
    vn
    @70
    crab
    #
    chash
    cfv
    #
    @153
    @157
    @149
    chash
    @156
    @148
    vn
    @70
    @85
    @70
    wcel
    #
    @155
    @85
    @34
    cdvds
    @159
    @85
    @159
    @85
    @85
    cN
    elfznn
    nncnd
    subid1d
    breq2d
    rabbiia
    fveq2i
    @61
    @158
    cN
    cc0
    cmin
    co
    #
    @34
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    c1
    cmin
    co
    #
    cc0
    cmin
    co
    #
    @34
    cdiv
    co
    #
    cfl
    cfv
    #
    cmin
    co
    @153
    cc0
    cmin
    co
    @153
    @61
    vn
    c1
    cN
    cc0
    @34
    @133
    @61
    1zzd
    wph
    cN
    @163
    cuz
    cfv
    #
    wcel
    @60
    wph
    cN
    cn0
    @167
    wph
    cN
    prmrec.3
    nnnn0d
    cn0
    cc0
    cuz
    cfv
    @167
    nn0uz
    @163
    cc0
    cuz
    1m1e0
    fveq2i
    eqtr4i
    syl6eleq
    adantr
    @61
    0zd
    hashdvds
    @61
    @162
    @153
    @166
    cc0
    cmin
    @61
    @161
    @152
    cfl
    @61
    @160
    cN
    @34
    cdiv
    @61
    cN
    @121
    subid1d
    oveq1d
    fveq2d
    @61
    @166
    cc0
    cfl
    cfv
    #
    cc0
    @61
    @165
    cc0
    cfl
    @61
    @165
    cc0
    @34
    cdiv
    co
    cc0
    @164
    cc0
    @34
    cdiv
    @164
    cc0
    cc0
    cmin
    co
    cc0
    @163
    cc0
    cc0
    cmin
    1m1e0
    oveq1i
    0m0e0
    eqtri
    oveq1i
    @61
    @34
    @61
    @34
    @133
    nncnd
    #
    @61
    @34
    @133
    nnne0d
    #
    div0d
    syl5eq
    fveq2d
    cc0
    cz
    wcel
    @168
    cc0
    wceq
    0z
    cc0
    flid
    ax-mp
    syl6eq
    oveq12d
    @61
    @153
    @61
    @153
    @61
    @152
    @154
    flcld
    zcnd
    subid1d
    3eqtrd
    syl5eqr
    @61
    @152
    @151
    @61
    cN
    @34
    @121
    @169
    @170
    divrecd
    eqcomd
    3brtr4d
    adantr
    @147
    @123
    @149
    chash
    @147
    @123
    @62
    @148
    wa
    #
    vn
    @70
    crab
    #
    @149
    @61
    @123
    @172
    wceq
    #
    @62
    @61
    @105
    @173
    @133
    vp
    @34
    @93
    @172
    cn
    cW
    @89
    @34
    wceq
    #
    @92
    @171
    vn
    @70
    @174
    @90
    @62
    @91
    @148
    @89
    @34
    cprime
    eleq1
    @89
    @34
    @85
    cdvds
    breq1
    anbi12d
    rabbidv
    prmrec.7
    @171
    vn
    @70
    @95
    rabex
    fvmpt
    syl
    #
    adantr
    @147
    @148
    @171
    vn
    @70
    @147
    @62
    @148
    @61
    @62
    simpr
    biantrurd
    rabbidv
    eqtr4d
    fveq2d
    @147
    @64
    @63
    cN
    cmul
    @62
    @64
    @63
    wceq
    @61
    @62
    @63
    cc0
    iftrue
    adantl
    oveq2d
    3brtr4d
    @107
    cc0
    cc0
    @124
    @65
    cle
    cc0
    cc0
    cle
    wbr
    @107
    0le0
    a1i
    @107
    @124
    @53
    cc0
    @107
    @123
    c0
    chash
    @61
    @106
    @123
    @172
    c0
    @175
    @106
    @171
    wn
    #
    vn
    @70
    wral
    @172
    c0
    wceq
    @106
    @176
    vn
    @70
    @171
    @62
    @62
    @148
    simpl
    con3i
    ralrimivw
    @171
    vn
    @70
    rabeq0
    sylibr
    sylan9eq
    fveq2d
    hash0
    syl6eq
    @106
    @61
    @65
    @50
    cc0
    @106
    @64
    cc0
    cN
    cmul
    @62
    @63
    cc0
    iffalse
    oveq2d
    wph
    @50
    cc0
    wceq
    @60
    @52
    adantr
    sylan9eqr
    3brtr4d
    pm2.61dan
    leadd2dd
    letrd
    @61
    @37
    cr
    wcel
    @66
    cr
    wcel
    @39
    cr
    wcel
    @122
    @67
    wa
    @40
    wi
    @129
    @137
    @61
    cN
    @38
    @100
    @61
    @35
    @9
    vk
    @61
    @1
    @34
    fzfid
    @61
    wph
    @78
    @101
    @115
    @116
    @117
    @118
    @80
    @101
    @84
    @102
    syl
    syl2an
    fsumrecl
    remulcld
    @37
    @66
    @39
    letr
    syl3anc
    mpand
    sylbid
    expcom
    a2d
    uzind4
    com12
end
