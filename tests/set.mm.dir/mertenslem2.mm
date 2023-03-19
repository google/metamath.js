include "cv.mm"
include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "cfv.mm"
include "cn0.mm"
include "csu.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "c2.mm"
include "cdiv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "cfz.mm"
include "cmul.mm"
include "nnuz.mm"
include "1zzd.mm"
include "rphalfcld.mm"
include "nn0uz.mm"
include "0zd.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "cr.mm"
include "abscld.mm"
include "eqeltrd.mm"
include "isumrecl.mm"
include "cle.mm"
include "absge0d.mm"
include "breqtrrd.mm"
include "isumge0.mm"
include "ge0p1rpd.mm"
include "rpdivcld.mm"
include "isumclim2.mm"
include "climi2.mm"
include "wb.mm"
include "eluznn.mm"
include "cc.mm"
include "wf.mm"
include "serf.mm"
include "nnnn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "isumcl.mm"
include "adantr.mm"
include "abssubd.mm"
include "eqid.mm"
include "adantl.mm"
include "peano2nn0.mm"
include "syl.mm"
include "nn0zd.mm"
include "wceq.mm"
include "simpll.mm"
include "eluznn0.mm"
include "sylan.mm"
include "syl2anc.mm"
include "cli.mm"
include "cdm.mm"
include "adantlr.mm"
include "iserex.mm"
include "mpbid.mm"
include "pncan2d.mm"
include "isumsplit.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "simpl.mm"
include "elfznn0.mm"
include "syl6eleq.mm"
include "fsumser.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "3eqtr4d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "weq.mm"
include "oveq1.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "csup.mm"
include "cmpt.mm"
include "crp.mm"
include "simplbi.mm"
include "nnrpd.mm"
include "cab.mm"
include "wi.mm"
include "simplll.mm"
include "ad2antrr.mm"
include "eleq1a.mm"
include "rexlimdva.mm"
include "abssdv.mm"
include "syl5eqss.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "fzfid.mm"
include "abrexfi.mm"
include "syl5eqel.mm"
include "nnm1nn0.mm"
include "eluzfz1.mm"
include "eqcomd.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "fvex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab2.mm"
include "sylibr.mm"
include "ne0i.mm"
include "wor.mm"
include "w3a.mm"
include "ltso.mm"
include "fisupcl.mm"
include "mpan.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "0red.mm"
include "1nn0.mm"
include "a1i.mm"
include "fimaxre2.mm"
include "3jca.mm"
include "suprub.mm"
include "letrd.mm"
include "fveq2.mm"
include "fvmpt.mm"
include "cvv.mm"
include "nn0ex.mm"
include "mptex.mm"
include "elnn0uz.mm"
include "sylan2br.mm"
include "seqfeq.mm"
include "recnd.mm"
include "serf0.mm"
include "climi0.mm"
include "adantll.mm"
include "absidd.mm"
include "ralrimiva.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "syl6bbr.mm"
include "anbi2i.mm"
include "biimpi.mm"
include "jca.mm"
include "mertenslem1.mm"
include "expr.mm"
include "sylbid.mm"
include "mpd.mm"
include "ex.mm"
include "syl5bir.mm"
include "expdimp.mm"

theorem mertenslem2
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cT: class T
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vi: setvar i
  let vl: setvar l
  let vu: setvar u
  let vw: setvar w
  assume mertens.1: |- ( ( ph /\ j e. NN0 ) -> ( F ` j ) = A )
  assume mertens.2: |- ( ( ph /\ j e. NN0 ) -> ( K ` j ) = ( abs ` A ) )
  assume mertens.3: |- ( ( ph /\ j e. NN0 ) -> A e. CC )
  assume mertens.4: |- ( ( ph /\ k e. NN0 ) -> ( G ` k ) = B )
  assume mertens.5: |- ( ( ph /\ k e. NN0 ) -> B e. CC )
  assume mertens.6: |- ( ( ph /\ k e. NN0 ) -> ( H ` k ) = sum_ j e. ( 0 ... k ) ( A x. ( G ` ( k - j ) ) ) )
  assume mertens.7: |- ( ph -> seq 0 ( + , K ) e. dom ~~> )
  assume mertens.8: |- ( ph -> seq 0 ( + , G ) e. dom ~~> )
  assume mertens.9: |- ( ph -> E e. RR+ )
  assume mertens.10: |- T = { z | E. n e. ( 0 ... ( s - 1 ) ) z = ( abs ` sum_ k e. ( ZZ>= ` ( n + 1 ) ) ( G ` k ) ) }
  assume mertens.11: |- ( ps <-> ( s e. NN /\ A. n e. ( ZZ>= ` s ) ( abs ` sum_ k e. ( ZZ>= ` ( n + 1 ) ) ( G ` k ) ) < ( ( E / 2 ) / ( sum_ j e. NN0 ( K ` j ) + 1 ) ) ) )

  disjoint n s
  disjoint n ph
  disjoint ph s
  disjoint j m
  disjoint j n
  disjoint j s
  disjoint j y
  disjoint j z
  disjoint B j
  disjoint m n
  disjoint m s
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint n s
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint j k
  disjoint G j
  disjoint k m
  disjoint k n
  disjoint k s
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G s
  disjoint G y
  disjoint G z
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph y
  disjoint ph z
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A s
  disjoint A y
  disjoint E j
  disjoint E k
  disjoint E m
  disjoint E n
  disjoint E s
  disjoint E y
  disjoint E z
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K n
  disjoint K s
  disjoint K y
  disjoint K z
  disjoint F j
  disjoint F m
  disjoint F n
  disjoint F y
  disjoint j ps
  disjoint k ps
  disjoint m ps
  disjoint n ps
  disjoint ps y
  disjoint ps z
  disjoint T j
  disjoint T k
  disjoint T m
  disjoint T n
  disjoint T y
  disjoint T z
  disjoint H k
  disjoint H m
  disjoint H y
  disjoint n t
  disjoint s t
  disjoint ph t
  disjoint j t
  disjoint j x
  disjoint m t
  disjoint m x
  disjoint n t
  disjoint n x
  disjoint s t
  disjoint s x
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i n
  disjoint i s
  disjoint i u
  disjoint i y
  disjoint i z
  disjoint G i
  disjoint j l
  disjoint j u
  disjoint k l
  disjoint k u
  disjoint l m
  disjoint l n
  disjoint l s
  disjoint l u
  disjoint l y
  disjoint l z
  disjoint G l
  disjoint m u
  disjoint n u
  disjoint s u
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint k x
  disjoint ph x
  disjoint k t
  disjoint A t
  disjoint E t
  disjoint i t
  disjoint K i
  disjoint t u
  disjoint K t
  disjoint K u
  disjoint u x
  disjoint F u
  disjoint F x
  disjoint ps t
  disjoint j w
  disjoint k w
  disjoint m w
  disjoint n w
  disjoint t w
  disjoint T t
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint H x
  assert |- ( ph -> E. y e. NN0 A. m e. ( ZZ>= ` y ) ( abs ` sum_ j e. ( 0 ... m ) ( A x. sum_ k e. ( ZZ>= ` ( ( m - j ) + 1 ) ) B ) ) < E )

  proof
    wph
    vm
    cv
    #
    caddc
    cG
    cc0
    cseq
    #
    cfv
    #
    cn0
    cB
    vk
    csu
    #
    cmin
    co
    cabs
    cfv
    #
    cE
    c2
    cdiv
    co
    #
    cn0
    vj
    cv
    #
    cK
    cfv
    #
    vj
    csu
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    clt
    wbr
    #
    vm
    vs
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vs
    cn
    wrex
    cc0
    @0
    cfz
    co
    #
    cA
    @0
    @6
    cmin
    co
    c1
    caddc
    co
    cuz
    cfv
    cB
    vk
    csu
    cmul
    co
    vj
    csu
    cabs
    cfv
    cE
    clt
    wbr
    vm
    vy
    cv
    cuz
    cfv
    wral
    vy
    cn0
    wrex
    #
    wph
    @3
    @2
    @10
    vs
    vm
    @1
    c1
    cn
    nnuz
    wph
    1zzd
    #
    wph
    @5
    @9
    wph
    cE
    mertens.9
    rphalfcld
    #
    wph
    @8
    wph
    @7
    vj
    cK
    cc0
    cn0
    nn0uz
    wph
    0zd
    #
    wph
    @6
    cn0
    wcel
    #
    wa
    #
    @7
    eqidd
    #
    @21
    @7
    cA
    cabs
    cfv
    #
    cr
    mertens.2
    @21
    cA
    mertens.3
    abscld
    #
    eqeltrd
    #
    mertens.7
    isumrecl
    wph
    @7
    vj
    cK
    cc0
    cn0
    nn0uz
    @19
    @22
    @25
    mertens.7
    @21
    cc0
    @23
    @7
    cle
    @21
    cA
    mertens.3
    absge0d
    mertens.2
    breqtrrd
    #
    isumge0
    ge0p1rpd
    rpdivcld
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @2
    eqidd
    wph
    cB
    vk
    cG
    cc0
    cn0
    nn0uz
    @19
    mertens.4
    mertens.5
    mertens.8
    isumclim2
    climi2
    wph
    @14
    @16
    vs
    cn
    wph
    @12
    cn
    wcel
    #
    wa
    #
    @14
    vn
    cv
    #
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    vk
    cv
    #
    cG
    cfv
    #
    vk
    csu
    #
    cabs
    cfv
    #
    @10
    clt
    wbr
    #
    vn
    @13
    wral
    #
    @16
    @30
    @14
    @0
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @35
    vk
    csu
    #
    cabs
    cfv
    #
    @10
    clt
    wbr
    #
    vm
    @13
    wral
    @39
    @30
    @11
    @44
    vm
    @13
    wph
    @29
    @0
    @13
    wcel
    #
    @11
    @44
    wb
    #
    @29
    @45
    wa
    wph
    @27
    @46
    @0
    @12
    eluznn
    @28
    @4
    @43
    @10
    clt
    @28
    @4
    @3
    @2
    cmin
    co
    #
    cabs
    cfv
    @43
    @28
    @2
    @3
    wph
    cn0
    cc
    @1
    wf
    @0
    cn0
    wcel
    #
    @2
    cc
    wcel
    @27
    wph
    vk
    cG
    cc0
    cn0
    nn0uz
    @19
    wph
    @34
    cn0
    wcel
    #
    wa
    @35
    cB
    cc
    mertens.4
    mertens.5
    eqeltrd
    #
    serf
    @0
    nnnn0
    #
    cn0
    cc
    @0
    @1
    ffvelrn
    syl2an
    #
    wph
    @3
    cc
    wcel
    @27
    wph
    cB
    vk
    cG
    cc0
    cn0
    nn0uz
    @19
    mertens.4
    mertens.5
    mertens.8
    isumcl
    adantr
    abssubd
    @28
    @47
    @42
    cabs
    @28
    @2
    @41
    cB
    vk
    csu
    #
    caddc
    co
    #
    @2
    cmin
    co
    @53
    @47
    @42
    @28
    @2
    @53
    @52
    @28
    cB
    vk
    cG
    @40
    @41
    @41
    eqid
    #
    @28
    @40
    @28
    @48
    @40
    cn0
    wcel
    #
    @27
    @48
    wph
    @51
    adantl
    #
    @0
    peano2nn0
    syl
    #
    nn0zd
    @28
    @34
    @41
    wcel
    #
    wa
    #
    wph
    @49
    @35
    cB
    wceq
    #
    wph
    @27
    @59
    simpll
    #
    @28
    @56
    @59
    @49
    @58
    @34
    @40
    eluznn0
    sylan
    #
    mertens.4
    syl2anc
    #
    @60
    wph
    @49
    cB
    cc
    wcel
    #
    @62
    @63
    mertens.5
    syl2anc
    @28
    @1
    cli
    cdm
    #
    wcel
    #
    caddc
    cG
    @40
    cseq
    @66
    wcel
    wph
    @67
    @27
    mertens.8
    adantr
    #
    @28
    vk
    cG
    cc0
    @40
    cn0
    nn0uz
    @58
    wph
    @49
    @35
    cc
    wcel
    #
    @27
    @50
    adantlr
    iserex
    mpbid
    isumcl
    pncan2d
    @28
    @3
    @54
    @2
    cmin
    @28
    @3
    cc0
    @40
    c1
    cmin
    co
    #
    cfz
    co
    #
    cB
    vk
    csu
    #
    @53
    caddc
    co
    @54
    @28
    cB
    vk
    cG
    cc0
    @40
    @41
    cn0
    nn0uz
    @55
    @58
    wph
    @49
    @61
    @27
    mertens.4
    adantlr
    wph
    @49
    @65
    @27
    mertens.5
    adantlr
    @68
    isumsplit
    @28
    @72
    @2
    @53
    caddc
    @28
    @72
    @15
    cB
    vk
    csu
    @2
    @28
    @71
    @15
    cB
    vk
    @28
    @70
    @0
    cc0
    cfz
    @28
    @0
    cc
    wcel
    #
    c1
    cc
    wcel
    @70
    @0
    wceq
    @27
    @73
    wph
    @0
    nncn
    adantl
    ax-1cn
    @0
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    @28
    cB
    vk
    cG
    cc0
    @0
    @28
    wph
    @49
    @61
    @34
    @15
    wcel
    #
    wph
    @27
    simpl
    #
    @34
    @0
    elfznn0
    #
    mertens.4
    syl2an
    @28
    @0
    cn0
    cc0
    cuz
    cfv
    #
    @57
    nn0uz
    syl6eleq
    @28
    wph
    @49
    @65
    @74
    @75
    @76
    mertens.5
    syl2an
    fsumser
    eqtrd
    oveq1d
    eqtrd
    oveq1d
    @28
    @41
    @35
    cB
    vk
    @64
    sumeq2dv
    3eqtr4d
    fveq2d
    eqtrd
    breq1d
    sylan2
    anassrs
    ralbidva
    @44
    @38
    vm
    vn
    @13
    vm
    vn
    weq
    #
    @43
    @37
    @10
    clt
    @78
    @42
    @36
    cabs
    @78
    @41
    @33
    @35
    vk
    @78
    @40
    @32
    cuz
    @0
    @31
    c1
    caddc
    oveq1
    fveq2d
    sumeq1d
    fveq2d
    breq1d
    cbvralv
    syl6bb
    wph
    @29
    @39
    @16
    @29
    @39
    wa
    wps
    wph
    @16
    mertens.11
    wph
    wps
    @16
    wph
    wps
    wa
    #
    @0
    cK
    cfv
    #
    cabs
    cfv
    #
    @5
    @12
    cdiv
    co
    #
    cT
    cr
    clt
    csup
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    clt
    wbr
    #
    vm
    vt
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vt
    cn0
    wrex
    @16
    @79
    @80
    @85
    vt
    vm
    vn
    cn0
    @31
    cK
    cfv
    #
    cmpt
    #
    cc0
    cn0
    nn0uz
    @79
    0zd
    @79
    @82
    @84
    @79
    @5
    @12
    wph
    @5
    crp
    wcel
    wps
    @18
    adantr
    @79
    @12
    wps
    @29
    wph
    wps
    @29
    @39
    mertens.11
    simplbi
    adantl
    #
    nnrpd
    rpdivcld
    @79
    @83
    @79
    cT
    cr
    @83
    @79
    cT
    vz
    cv
    #
    @37
    wceq
    #
    vn
    cc0
    @12
    c1
    cmin
    co
    #
    cfz
    co
    #
    wrex
    #
    vz
    cab
    #
    cr
    mertens.10
    @79
    @97
    vz
    cr
    @79
    @94
    @93
    cr
    wcel
    #
    vn
    @96
    @79
    @31
    @96
    wcel
    #
    wa
    #
    @37
    cr
    wcel
    @94
    @99
    wi
    @101
    @36
    @101
    @35
    vk
    cG
    @32
    @33
    @33
    eqid
    @101
    @32
    @101
    @31
    cn0
    wcel
    #
    @32
    cn0
    wcel
    #
    @100
    @102
    @79
    @31
    @95
    elfznn0
    adantl
    @31
    peano2nn0
    syl
    #
    nn0zd
    @101
    @34
    @33
    wcel
    #
    wa
    #
    @35
    eqidd
    @106
    wph
    @49
    @69
    wph
    wps
    @100
    @105
    simplll
    @101
    @103
    @105
    @49
    @104
    @34
    @32
    eluznn0
    sylan
    @50
    syl2anc
    @101
    @67
    caddc
    cG
    @32
    cseq
    @66
    wcel
    wph
    @67
    wps
    @100
    mertens.8
    ad2antrr
    @101
    vk
    cG
    cc0
    @32
    cn0
    nn0uz
    @104
    @101
    wph
    @49
    @69
    wph
    wps
    @100
    simpll
    @50
    sylan
    iserex
    mpbid
    isumcl
    abscld
    @37
    cr
    @93
    eleq1a
    syl
    rexlimdva
    abssdv
    syl5eqss
    #
    @79
    cT
    cfn
    wcel
    #
    cT
    c0
    wne
    #
    cT
    cr
    wss
    #
    @83
    cT
    wcel
    #
    @79
    cT
    @98
    cfn
    mertens.10
    @79
    @96
    cfn
    wcel
    @98
    cfn
    wcel
    @79
    cc0
    @95
    fzfid
    vn
    vz
    @96
    @37
    abrexfi
    syl
    syl5eqel
    #
    @79
    cn
    cB
    vk
    csu
    #
    cabs
    cfv
    #
    cT
    wcel
    #
    @109
    @79
    @114
    @37
    wceq
    #
    vn
    @96
    wrex
    #
    @115
    @79
    cc0
    @96
    wcel
    #
    @114
    cn
    @35
    vk
    csu
    #
    cabs
    cfv
    #
    wceq
    #
    @117
    @79
    @95
    @77
    wcel
    @118
    @79
    @95
    cn0
    @77
    @79
    @29
    @95
    cn0
    wcel
    @92
    @12
    nnm1nn0
    syl
    nn0uz
    syl6eleq
    cc0
    @95
    eluzfz1
    syl
    @79
    @120
    @114
    @79
    @119
    @113
    cabs
    wph
    @119
    @113
    wceq
    wps
    wph
    cn
    @35
    cB
    vk
    @34
    cn
    wcel
    #
    wph
    @49
    @61
    @34
    nnnn0
    #
    mertens.4
    sylan2
    #
    sumeq2dv
    adantr
    fveq2d
    eqcomd
    @116
    @121
    vn
    cc0
    @96
    @31
    cc0
    wceq
    #
    @37
    @120
    @114
    @125
    @36
    @119
    cabs
    @125
    @33
    cn
    @35
    vk
    @125
    @33
    c1
    cuz
    cfv
    cn
    @125
    @32
    c1
    cuz
    @125
    @32
    cc0
    c1
    caddc
    co
    c1
    @31
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    nnuz
    syl6eqr
    sumeq1d
    fveq2d
    eqeq2d
    rspcev
    syl2anc
    @97
    @117
    vz
    @114
    cT
    @113
    cabs
    fvex
    @93
    @114
    wceq
    @94
    @116
    vn
    @96
    @93
    @114
    @37
    eqeq1
    rexbidv
    mertens.10
    elab2
    sylibr
    #
    cT
    @114
    ne0i
    syl
    #
    @107
    cr
    clt
    wor
    @108
    @109
    @110
    w3a
    @111
    ltso
    cr
    cT
    clt
    fisupcl
    mpan
    syl3anc
    sseldd
    #
    @79
    cc0
    @114
    @83
    @79
    0red
    @79
    @113
    wph
    @113
    cc
    wcel
    wps
    wph
    cB
    vk
    cG
    c1
    cn
    nnuz
    @17
    @124
    @122
    wph
    @49
    @65
    @123
    mertens.5
    sylan2
    wph
    @67
    caddc
    cG
    c1
    cseq
    @66
    wcel
    mertens.8
    wph
    vk
    cG
    cc0
    c1
    cn0
    nn0uz
    c1
    cn0
    wcel
    wph
    1nn0
    a1i
    @50
    iserex
    mpbid
    isumcl
    adantr
    #
    abscld
    @128
    @79
    @113
    @129
    absge0d
    @79
    @110
    @109
    vw
    cv
    @93
    cle
    wbr
    vw
    cT
    wral
    vz
    cr
    wrex
    #
    w3a
    #
    @115
    @114
    @83
    cle
    wbr
    @79
    @110
    @109
    @130
    @107
    @127
    @79
    @110
    @108
    @130
    @107
    @112
    vz
    vw
    cT
    fimaxre2
    syl2anc
    3jca
    #
    @126
    vz
    vw
    cT
    @114
    suprub
    syl2anc
    letrd
    #
    ge0p1rpd
    rpdivcld
    @48
    @0
    @91
    cfv
    @80
    wceq
    @79
    vn
    @0
    @90
    @80
    cn0
    @91
    @31
    @0
    cK
    fveq2
    #
    @91
    eqid
    #
    @0
    cK
    fvex
    fvmpt
    adantl
    wph
    @91
    cc0
    cli
    wbr
    wps
    wph
    vj
    @91
    cc0
    cvv
    cn0
    nn0uz
    @19
    @91
    cvv
    wcel
    wph
    vn
    cn0
    @90
    nn0ex
    mptex
    a1i
    wph
    caddc
    @91
    cc0
    cseq
    caddc
    cK
    cc0
    cseq
    #
    @66
    wph
    caddc
    vj
    @91
    cK
    cc0
    @19
    @6
    @77
    wcel
    wph
    @20
    @6
    @91
    cfv
    #
    @7
    wceq
    #
    @6
    elnn0uz
    @20
    @138
    wph
    vn
    @6
    @90
    @7
    cn0
    @91
    @31
    @6
    cK
    fveq2
    @135
    @6
    cK
    fvex
    fvmpt
    adantl
    #
    sylan2br
    seqfeq
    mertens.7
    eqeltrd
    @21
    @137
    @21
    @137
    @23
    cr
    @21
    @137
    @7
    @23
    @139
    mertens.2
    eqtrd
    @24
    eqeltrd
    recnd
    serf0
    adantr
    climi0
    @79
    @89
    @16
    vt
    cn0
    @79
    @87
    cn0
    wcel
    #
    wa
    #
    @89
    @90
    @85
    clt
    wbr
    #
    vn
    @88
    wral
    #
    @16
    @141
    @89
    @80
    @85
    clt
    wbr
    #
    vm
    @88
    wral
    #
    @143
    @141
    @86
    @144
    vm
    @88
    @141
    @0
    @88
    wcel
    #
    wa
    #
    @81
    @80
    @85
    clt
    @147
    wph
    @48
    @81
    @80
    wceq
    #
    wph
    wps
    @140
    @146
    simplll
    @140
    @146
    @48
    @79
    @0
    @87
    eluznn0
    adantll
    wph
    @7
    cabs
    cfv
    #
    @7
    wceq
    #
    vj
    cn0
    wral
    @48
    @148
    wph
    @150
    vj
    cn0
    @21
    @7
    @25
    @26
    absidd
    ralrimiva
    @150
    @148
    vj
    @0
    cn0
    vj
    vm
    weq
    #
    @149
    @81
    @7
    @80
    @151
    @7
    @80
    cabs
    @6
    @0
    cK
    fveq2
    #
    fveq2d
    @152
    eqeq12d
    rspccva
    sylan
    syl2anc
    breq1d
    ralbidva
    @142
    @144
    vn
    vm
    @88
    vn
    vm
    weq
    @90
    @80
    @85
    clt
    @134
    breq1d
    cbvralv
    #
    syl6bbr
    @79
    @140
    @143
    @16
    @79
    @140
    @143
    wa
    #
    wa
    #
    wps
    vy
    vz
    vw
    vt
    cA
    cB
    cT
    vj
    vk
    vm
    vn
    cE
    cF
    cG
    cH
    cK
    vs
    @155
    wph
    @20
    @6
    cF
    cfv
    cA
    wceq
    wph
    wps
    @154
    simpll
    #
    mertens.1
    sylan
    @155
    wph
    @20
    @7
    @23
    wceq
    @156
    mertens.2
    sylan
    @155
    wph
    @20
    cA
    cc
    wcel
    @156
    mertens.3
    sylan
    @155
    wph
    @49
    @61
    @156
    mertens.4
    sylan
    @155
    wph
    @49
    @65
    @156
    mertens.5
    sylan
    @155
    wph
    @49
    @34
    cH
    cfv
    cc0
    @34
    cfz
    co
    cA
    @34
    @6
    cmin
    co
    cG
    cfv
    cmul
    co
    vj
    csu
    wceq
    @156
    mertens.6
    sylan
    wph
    @136
    @66
    wcel
    wps
    @154
    mertens.7
    ad2antrr
    wph
    @67
    wps
    @154
    mertens.8
    ad2antrr
    wph
    cE
    crp
    wcel
    wps
    @154
    mertens.9
    ad2antrr
    mertens.10
    mertens.11
    wps
    @154
    wps
    @140
    @145
    wa
    #
    wa
    #
    wph
    wps
    @154
    wa
    @158
    @154
    @157
    wps
    @143
    @145
    @140
    @153
    anbi2i
    anbi2i
    biimpi
    adantll
    @79
    cc0
    @83
    cle
    wbr
    #
    @131
    wa
    @154
    @79
    @159
    @131
    @133
    @132
    jca
    adantr
    mertenslem1
    expr
    sylbid
    rexlimdva
    mpd
    ex
    syl5bir
    expdimp
    sylbid
    rexlimdva
    mpd
end
