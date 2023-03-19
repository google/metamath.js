include "cdvn.mm"
include "co.mm"
include "cfv.mm"
include "cfa.mm"
include "cv.mm"
include "cprod.mm"
include "cdiv.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "wral.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "prodeq1.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "sumeq1d.mm"
include "oveq12d.mm"
include "sumeq2ad.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "a1i.mm"
include "eqcomd.mm"
include "wi.mm"
include "wa.mm"
include "c1.mm"
include "prod0.mm"
include "mpteq2i.mm"
include "oveq2i.mm"
include "id.mm"
include "fveq12d.mm"
include "adantl.mm"
include "cc.mm"
include "wss.mm"
include "cpm.mm"
include "cr.mm"
include "cpr.mm"
include "recnprss.mm"
include "syl.mm"
include "cdm.mm"
include "wf.mm"
include "1cnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "1re.mm"
include "rgenw.mm"
include "dmmptg.mm"
include "ax-mp.mm"
include "feq2d.mm"
include "mpbird.mm"
include "cpw.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "restsspw.mm"
include "sseldi.mm"
include "elpwi.mm"
include "eqsstrd.mm"
include "jca.mm"
include "cvv.mm"
include "wb.mm"
include "cnex.mm"
include "elpm2g.mm"
include "syl2anc.mm"
include "dvn0.mm"
include "adantr.mm"
include "cif.mm"
include "crab.mm"
include "cn0.mm"
include "cmap.mm"
include "oveq2.mm"
include "wal.mm"
include "wfn.mm"
include "elmapfn.mm"
include "fn0.mm"
include "sylib.mm"
include "velsn.mm"
include "sylibr.mm"
include "biimpi.mm"
include "f0.mm"
include "ovex.mm"
include "0ex.mm"
include "elmap.mm"
include "mpbir.mm"
include "eqeltrd.mm"
include "impbii.mm"
include "ax-gen.mm"
include "dfcleq.mm"
include "rabeq.mm"
include "sumeq1.mm"
include "eqeq1d.mm"
include "rabbidv.mm"
include "0elpw.mm"
include "nn0ex.mm"
include "mptex.mm"
include "fvmptd.mm"
include "eqeq2.mm"
include "0nn0.mm"
include "p0ex.mm"
include "rabex.mm"
include "snidg.mm"
include "pm3.2i.mm"
include "sum0.mm"
include "elrab.mm"
include "n0ii.mm"
include "wo.mm"
include "rabrsn.mm"
include "mtpor.mm"
include "iftrue.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"
include "fac0.mm"
include "oveq1d.mm"
include "1div1e1.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "ad2antlr.mm"
include "1t1e1.mm"
include "sumeq2dv.mm"
include "ax-1cn.mm"
include "eqidd.mm"
include "sumsn.mm"
include "mp2an.mm"
include "a1d.mm"
include "wn.mm"
include "fveq1i.mm"
include "cn.mm"
include "wne.mm"
include "elfznn0.mm"
include "neqne.mm"
include "elnnne0.mm"
include "adantll.mm"
include "dvnmptconst.mm"
include "ad2antrr.mm"
include "simpll.mm"
include "pm2.65da.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "adantlr.mm"
include "eqtr2d.mm"
include "ex.mm"
include "pm2.61dan.mm"
include "ralrimiv.mm"
include "cdif.mm"
include "prodeq2ad.mm"
include "cbvprodv.mm"
include "cbvmptv.mm"
include "fveq2d.mm"
include "fveq1.mm"
include "cbvsumv.mm"
include "eqeq12i.mm"
include "ralbii.mm"
include "simpr.mm"
include "cmin.mm"
include "cres.mm"
include "cop.mm"
include "ad3antrrr.mm"
include "cfn.mm"
include "simp-4l.mm"
include "w3a.mm"
include "simplll.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "feq1d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "syl3anc.mm"
include "simprl.mm"
include "simprr.mm"
include "eqcomi.mm"
include "cbvralv.mm"
include "reseq1.mm"
include "opeq12d.mm"
include "dvnprodlem2.mm"
include "syl21anc.mm"
include "findcard2d.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "rspccva.mm"
include "pwidg.mm"

theorem dvnprodlem3
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vc: setvar c
  let vd: setvar d
  let vh: setvar h
  let vk: setvar k
  let vl: setvar l
  let vr: setvar r
  let vz: setvar z
  let vy: setvar y
  let vu: setvar u
  assume dvnprodlem3.s: |- ( ph -> S e. { RR , CC } )
  assume dvnprodlem3.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume dvnprodlem3.t: |- ( ph -> T e. Fin )
  assume dvnprodlem3.h: |- ( ( ph /\ t e. T ) -> ( H ` t ) : X --> CC )
  assume dvnprodlem3.n: |- ( ph -> N e. NN0 )
  assume dvnprodlem3.dvnh: |- ( ( ph /\ t e. T /\ j e. ( 0 ... N ) ) -> ( ( S Dn ( H ` t ) ) ` j ) : X --> CC )
  assume dvnprodlem3.f: |- F = ( x e. X |-> prod_ t e. T ( ( H ` t ) ` x ) )
  assume dvnprodlem3.d: |- D = ( s e. ~P T |-> ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m s ) | sum_ t e. s ( c ` t ) = n } ) )
  assume dvnprodlem3.c: |- C = ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m T ) | sum_ t e. T ( c ` t ) = n } )

  disjoint C c
  disjoint D c
  disjoint D j
  disjoint D t
  disjoint c j
  disjoint c t
  disjoint j t
  disjoint D n
  disjoint D s
  disjoint D x
  disjoint c n
  disjoint c s
  disjoint c x
  disjoint j n
  disjoint j s
  disjoint j x
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint s t
  disjoint s x
  disjoint t x
  disjoint F s
  disjoint H c
  disjoint H j
  disjoint H t
  disjoint H n
  disjoint H s
  disjoint H x
  disjoint N c
  disjoint N j
  disjoint N t
  disjoint N n
  disjoint N s
  disjoint N x
  disjoint S c
  disjoint S j
  disjoint S t
  disjoint S n
  disjoint S s
  disjoint S x
  disjoint T c
  disjoint T j
  disjoint T t
  disjoint T n
  disjoint T s
  disjoint T x
  disjoint X c
  disjoint X j
  disjoint X t
  disjoint X n
  disjoint X s
  disjoint X x
  disjoint c ph
  disjoint j ph
  disjoint ph t
  disjoint n ph
  disjoint ph s
  disjoint ph x
  disjoint D d
  disjoint D h
  disjoint D k
  disjoint D l
  disjoint D r
  disjoint D z
  disjoint c d
  disjoint c h
  disjoint c k
  disjoint c l
  disjoint c r
  disjoint c z
  disjoint d h
  disjoint d j
  disjoint d k
  disjoint d l
  disjoint d r
  disjoint d t
  disjoint d z
  disjoint h j
  disjoint h k
  disjoint h l
  disjoint h r
  disjoint h t
  disjoint h z
  disjoint j k
  disjoint j l
  disjoint j r
  disjoint j z
  disjoint k l
  disjoint k r
  disjoint k t
  disjoint k z
  disjoint l r
  disjoint l t
  disjoint l z
  disjoint r t
  disjoint r z
  disjoint t z
  disjoint d n
  disjoint d s
  disjoint d x
  disjoint k n
  disjoint k s
  disjoint k x
  disjoint l n
  disjoint l s
  disjoint l x
  disjoint n r
  disjoint n z
  disjoint r s
  disjoint r x
  disjoint s z
  disjoint x z
  disjoint D y
  disjoint c y
  disjoint d y
  disjoint h y
  disjoint k y
  disjoint l y
  disjoint r y
  disjoint t y
  disjoint F k
  disjoint H d
  disjoint H h
  disjoint H k
  disjoint H l
  disjoint H r
  disjoint H z
  disjoint H u
  disjoint H y
  disjoint c u
  disjoint d u
  disjoint h u
  disjoint l u
  disjoint r u
  disjoint t u
  disjoint u y
  disjoint N h
  disjoint N k
  disjoint N l
  disjoint N r
  disjoint N z
  disjoint S d
  disjoint S h
  disjoint S k
  disjoint S l
  disjoint S r
  disjoint S z
  disjoint S u
  disjoint S y
  disjoint T h
  disjoint T k
  disjoint T l
  disjoint T r
  disjoint T z
  disjoint X h
  disjoint X k
  disjoint X l
  disjoint X r
  disjoint X z
  disjoint X y
  disjoint h ph
  disjoint k ph
  disjoint l ph
  disjoint ph r
  disjoint ph z
  disjoint n u
  disjoint n y
  disjoint s u
  disjoint s y
  disjoint u x
  disjoint x y
  disjoint k x
  assert |- ( ph -> ( ( S Dn F ) ` N ) = ( x e. X |-> sum_ c e. ( C ` N ) ( ( ( ! ` N ) / prod_ t e. T ( ! ` ( c ` t ) ) ) x. prod_ t e. T ( ( ( S Dn ( H ` t ) ) ` ( c ` t ) ) ` x ) ) ) )

  proof
    wph
    cN
    cS
    cF
    cdvn
    co
    #
    cfv
    #
    vx
    cX
    cN
    cT
    cD
    cfv
    #
    cfv
    #
    cN
    cfa
    cfv
    #
    cT
    vt
    cv
    #
    vc
    cv
    #
    cfv
    #
    cfa
    cfv
    #
    vt
    cprod
    #
    cdiv
    co
    #
    cT
    vx
    cv
    #
    @7
    cS
    @5
    cH
    cfv
    #
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    vt
    cprod
    #
    cmul
    co
    #
    vc
    csu
    #
    cmpt
    #
    vx
    cX
    cN
    cC
    cfv
    #
    @17
    vc
    csu
    #
    cmpt
    wph
    vk
    cv
    #
    @0
    cfv
    #
    vx
    cX
    @22
    @2
    cfv
    #
    @22
    cfa
    cfv
    #
    @9
    cdiv
    co
    #
    @16
    cmul
    co
    #
    vc
    csu
    #
    cmpt
    #
    wceq
    #
    vk
    cc0
    cN
    cfz
    co
    #
    wral
    #
    cN
    @31
    wcel
    #
    @1
    @19
    wceq
    #
    wph
    @22
    cS
    vx
    cX
    vs
    cv
    #
    @11
    @12
    cfv
    #
    vt
    cprod
    #
    cmpt
    #
    cdvn
    co
    #
    cfv
    #
    vx
    cX
    @22
    @35
    cD
    cfv
    #
    cfv
    #
    @25
    @35
    @8
    vt
    cprod
    #
    cdiv
    co
    #
    @35
    @15
    vt
    cprod
    #
    cmul
    co
    #
    vc
    csu
    #
    cmpt
    #
    wceq
    #
    vk
    @31
    wral
    @22
    cS
    vx
    cX
    c0
    @36
    vt
    cprod
    #
    cmpt
    #
    cdvn
    co
    #
    cfv
    #
    vx
    cX
    @22
    c0
    cD
    cfv
    #
    cfv
    #
    @25
    c0
    @8
    vt
    cprod
    #
    cdiv
    co
    #
    c0
    @15
    vt
    cprod
    #
    cmul
    co
    #
    vc
    csu
    #
    cmpt
    #
    wceq
    #
    vk
    @31
    wral
    @22
    cS
    vx
    cX
    vr
    cv
    #
    @36
    vt
    cprod
    #
    cmpt
    #
    cdvn
    co
    #
    cfv
    #
    vx
    cX
    @22
    @63
    cD
    cfv
    #
    cfv
    #
    @25
    @63
    @8
    vt
    cprod
    #
    cdiv
    co
    #
    @63
    @15
    vt
    cprod
    #
    cmul
    co
    #
    vc
    csu
    #
    cmpt
    #
    wceq
    #
    vk
    @31
    wral
    #
    @22
    cS
    vx
    cX
    @63
    vz
    cv
    #
    csn
    cun
    #
    @36
    vt
    cprod
    #
    cmpt
    #
    cdvn
    co
    #
    cfv
    #
    vx
    cX
    @22
    @79
    cD
    cfv
    #
    cfv
    #
    @25
    @79
    @8
    vt
    cprod
    #
    cdiv
    co
    #
    @79
    @15
    vt
    cprod
    #
    cmul
    co
    #
    vc
    csu
    #
    cmpt
    #
    wceq
    #
    vk
    @31
    wral
    #
    @32
    vs
    vr
    vz
    cT
    @35
    c0
    wceq
    #
    @49
    @62
    vk
    @31
    @94
    @40
    @53
    @48
    @61
    @94
    @22
    @39
    @52
    @94
    @38
    @51
    cS
    cdvn
    @94
    vx
    cX
    @37
    @50
    @35
    c0
    @36
    vt
    prodeq1
    mpteq2dv
    oveq2d
    fveq1d
    @94
    vx
    cX
    @47
    @60
    @94
    @47
    @55
    @46
    vc
    csu
    @60
    @94
    @42
    @55
    @46
    vc
    @94
    @22
    @41
    @54
    @35
    c0
    cD
    fveq2
    fveq1d
    sumeq1d
    @94
    @55
    @46
    @59
    vc
    @94
    @44
    @57
    @45
    @58
    cmul
    @94
    @43
    @56
    @25
    cdiv
    @35
    c0
    @8
    vt
    prodeq1
    oveq2d
    @35
    c0
    @15
    vt
    prodeq1
    oveq12d
    sumeq2ad
    eqtrd
    mpteq2dv
    eqeq12d
    ralbidv
    @35
    @63
    wceq
    #
    @49
    @76
    vk
    @31
    @95
    @40
    @67
    @48
    @75
    @95
    @22
    @39
    @66
    @95
    @38
    @65
    cS
    cdvn
    @95
    vx
    cX
    @37
    @64
    @35
    @63
    @36
    vt
    prodeq1
    mpteq2dv
    oveq2d
    fveq1d
    @95
    vx
    cX
    @47
    @74
    @95
    @47
    @69
    @46
    vc
    csu
    @74
    @95
    @42
    @69
    @46
    vc
    @95
    @22
    @41
    @68
    @35
    @63
    cD
    fveq2
    fveq1d
    sumeq1d
    @95
    @69
    @46
    @73
    vc
    @95
    @44
    @71
    @45
    @72
    cmul
    @95
    @43
    @70
    @25
    cdiv
    @35
    @63
    @8
    vt
    prodeq1
    oveq2d
    @35
    @63
    @15
    vt
    prodeq1
    oveq12d
    sumeq2ad
    eqtrd
    mpteq2dv
    eqeq12d
    ralbidv
    @35
    @79
    wceq
    #
    @49
    @92
    vk
    @31
    @96
    @40
    @83
    @48
    @91
    @96
    @22
    @39
    @82
    @96
    @38
    @81
    cS
    cdvn
    @96
    vx
    cX
    @37
    @80
    @35
    @79
    @36
    vt
    prodeq1
    mpteq2dv
    oveq2d
    fveq1d
    @96
    vx
    cX
    @47
    @90
    @96
    @47
    @85
    @46
    vc
    csu
    @90
    @96
    @42
    @85
    @46
    vc
    @96
    @22
    @41
    @84
    @35
    @79
    cD
    fveq2
    fveq1d
    sumeq1d
    @96
    @85
    @46
    @89
    vc
    @96
    @44
    @87
    @45
    @88
    cmul
    @96
    @43
    @86
    @25
    cdiv
    @35
    @79
    @8
    vt
    prodeq1
    oveq2d
    @35
    @79
    @15
    vt
    prodeq1
    oveq12d
    sumeq2ad
    eqtrd
    mpteq2dv
    eqeq12d
    ralbidv
    @35
    cT
    wceq
    #
    @49
    @30
    vk
    @31
    @97
    @40
    @23
    @48
    @29
    @97
    @22
    @39
    @0
    @97
    @38
    cF
    cS
    cdvn
    @97
    @38
    vx
    cX
    cT
    @36
    vt
    cprod
    #
    cmpt
    #
    cF
    @97
    vx
    cX
    @37
    @98
    @35
    cT
    @36
    vt
    prodeq1
    mpteq2dv
    @97
    cF
    @99
    cF
    @99
    wceq
    @97
    dvnprodlem3.f
    a1i
    eqcomd
    eqtrd
    oveq2d
    fveq1d
    @97
    vx
    cX
    @47
    @28
    @97
    @47
    @24
    @46
    vc
    csu
    @28
    @97
    @42
    @24
    @46
    vc
    @97
    @22
    @41
    @2
    @35
    cT
    cD
    fveq2
    fveq1d
    sumeq1d
    @97
    @24
    @46
    @27
    vc
    @97
    @44
    @26
    @45
    @16
    cmul
    @97
    @43
    @9
    @25
    cdiv
    @35
    cT
    @8
    vt
    prodeq1
    oveq2d
    @35
    cT
    @15
    vt
    prodeq1
    oveq12d
    sumeq2ad
    eqtrd
    mpteq2dv
    eqeq12d
    ralbidv
    wph
    @62
    vk
    @31
    wph
    @22
    cc0
    wceq
    #
    @22
    @31
    wcel
    #
    @62
    wi
    wph
    @100
    wa
    #
    @62
    @101
    @102
    @53
    cc0
    cS
    vx
    cX
    c1
    cmpt
    #
    cdvn
    co
    #
    cfv
    #
    @103
    @61
    @100
    @53
    @105
    wceq
    wph
    @100
    @22
    cc0
    @52
    @104
    @52
    @104
    wceq
    @100
    @51
    @103
    cS
    cdvn
    vx
    cX
    @50
    c1
    @36
    vt
    prod0
    mpteq2i
    oveq2i
    #
    a1i
    @100
    id
    fveq12d
    adantl
    wph
    @105
    @103
    wceq
    #
    @100
    wph
    cS
    cc
    wss
    #
    @103
    cc
    cS
    cpm
    co
    wcel
    #
    @107
    wph
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    @108
    dvnprodlem3.s
    cS
    recnprss
    syl
    wph
    @109
    @103
    cdm
    #
    cc
    @103
    wf
    #
    @112
    cS
    wss
    #
    wa
    #
    wph
    @113
    @114
    wph
    @113
    cX
    cc
    @103
    wf
    wph
    vx
    cX
    c1
    cc
    @103
    wph
    @11
    cX
    wcel
    wa
    1cnd
    @103
    eqid
    fmptd
    wph
    @112
    cX
    cc
    @103
    @112
    cX
    wceq
    #
    wph
    c1
    cr
    wcel
    #
    vx
    cX
    wral
    @116
    @117
    vx
    cX
    1re
    rgenw
    vx
    cX
    c1
    cr
    dmmptg
    ax-mp
    a1i
    #
    feq2d
    mpbird
    wph
    @112
    cX
    cS
    @118
    wph
    cX
    cS
    cpw
    #
    wcel
    cX
    cS
    wss
    wph
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    @119
    cX
    cS
    @120
    restsspw
    dvnprodlem3.x
    sseldi
    cX
    cS
    elpwi
    syl
    eqsstrd
    jca
    wph
    cc
    cvv
    wcel
    #
    @111
    @109
    @115
    wb
    @122
    wph
    cnex
    a1i
    dvnprodlem3.s
    cc
    cS
    @103
    cvv
    @110
    elpm2g
    syl2anc
    mpbird
    cS
    @103
    dvn0
    syl2anc
    adantr
    @102
    @61
    @103
    @102
    vx
    cX
    @60
    c1
    @102
    @60
    c0
    csn
    #
    @59
    vc
    csu
    @123
    c1
    vc
    csu
    #
    c1
    @102
    @55
    @123
    @59
    vc
    @102
    @55
    @100
    @123
    c0
    cif
    #
    @123
    @102
    @55
    cc0
    @54
    cfv
    #
    c0
    @7
    vt
    csu
    #
    cc0
    wceq
    #
    vc
    @123
    crab
    #
    @125
    @100
    @55
    @126
    wceq
    wph
    @22
    cc0
    @54
    fveq2
    adantl
    wph
    @126
    @129
    wceq
    @100
    wph
    vn
    cc0
    @127
    vn
    cv
    #
    wceq
    #
    vc
    @123
    crab
    #
    @129
    cn0
    @54
    cvv
    wph
    vs
    c0
    vn
    cn0
    @35
    @7
    vt
    csu
    #
    @130
    wceq
    #
    vc
    cc0
    @130
    cfz
    co
    #
    @35
    cmap
    co
    #
    crab
    #
    cmpt
    #
    vn
    cn0
    @132
    cmpt
    #
    cT
    cpw
    #
    cD
    cvv
    cD
    vs
    @140
    @138
    cmpt
    wceq
    wph
    dvnprodlem3.d
    a1i
    #
    @94
    @138
    @139
    wceq
    wph
    @94
    vn
    cn0
    @137
    @132
    @94
    @137
    @134
    vc
    @123
    crab
    #
    @132
    @94
    @136
    @123
    wceq
    @137
    @142
    wceq
    @94
    @136
    @135
    c0
    cmap
    co
    #
    @123
    @35
    c0
    @135
    cmap
    oveq2
    @143
    @123
    wceq
    #
    @94
    @144
    @11
    @143
    wcel
    #
    @11
    @123
    wcel
    #
    wb
    #
    vx
    wal
    @147
    vx
    @145
    @146
    @145
    @11
    c0
    wceq
    #
    @146
    @145
    @11
    c0
    wfn
    @148
    @11
    @135
    c0
    elmapfn
    @11
    fn0
    sylib
    vx
    c0
    velsn
    #
    sylibr
    @146
    @148
    @145
    @146
    @148
    @149
    biimpi
    @148
    @11
    c0
    @143
    @148
    id
    c0
    @143
    wcel
    #
    @148
    @150
    c0
    @135
    c0
    wf
    @135
    f0
    @135
    c0
    c0
    cc0
    @130
    cfz
    ovex
    0ex
    elmap
    mpbir
    a1i
    eqeltrd
    syl
    impbii
    ax-gen
    vx
    @143
    @123
    dfcleq
    mpbir
    a1i
    eqtrd
    @134
    vc
    @136
    @123
    rabeq
    syl
    @94
    @134
    @131
    vc
    @123
    @94
    @133
    @127
    @130
    @35
    c0
    @7
    vt
    sumeq1
    eqeq1d
    rabbidv
    eqtrd
    mpteq2dv
    adantl
    c0
    @140
    wcel
    wph
    cT
    0elpw
    a1i
    @139
    cvv
    wcel
    wph
    vn
    cn0
    @132
    nn0ex
    mptex
    a1i
    fvmptd
    #
    @130
    cc0
    wceq
    #
    @132
    @129
    wceq
    wph
    @152
    @131
    @128
    vc
    @123
    @130
    cc0
    @127
    eqeq2
    rabbidv
    adantl
    cc0
    cn0
    wcel
    wph
    0nn0
    a1i
    @129
    cvv
    wcel
    wph
    @128
    vc
    @123
    p0ex
    rabex
    a1i
    fvmptd
    adantr
    @102
    @129
    @123
    @125
    @129
    @123
    wceq
    #
    @102
    @129
    c0
    wceq
    #
    @153
    c0
    @129
    c0
    @129
    wcel
    c0
    @123
    wcel
    #
    cc0
    cc0
    wceq
    #
    wa
    @155
    @156
    c0
    cvv
    wcel
    #
    @155
    0ex
    c0
    cvv
    snidg
    ax-mp
    cc0
    eqid
    pm3.2i
    @128
    @156
    vc
    c0
    @123
    @6
    c0
    wceq
    #
    @127
    cc0
    cc0
    @128
    @158
    @7
    vt
    sum0
    #
    a1i
    eqeq1d
    elrab
    mpbir
    n0ii
    @129
    @129
    wceq
    @154
    @153
    wo
    @129
    eqid
    @128
    vc
    c0
    @129
    rabrsn
    ax-mp
    mtpor
    a1i
    @100
    @125
    @123
    wceq
    wph
    @100
    @123
    c0
    iftrue
    adantl
    #
    eqtr4d
    3eqtrd
    @160
    eqtrd
    sumeq1d
    @102
    @123
    @59
    c1
    vc
    @102
    @6
    @123
    wcel
    #
    wa
    #
    @59
    c1
    c1
    cmul
    co
    #
    c1
    @100
    @59
    @163
    wceq
    wph
    @161
    @100
    @57
    c1
    @58
    c1
    cmul
    @100
    @57
    c1
    @56
    cdiv
    co
    #
    c1
    @100
    @25
    c1
    @56
    cdiv
    @100
    @25
    cc0
    cfa
    cfv
    #
    c1
    @22
    cc0
    cfa
    fveq2
    @165
    c1
    wceq
    @100
    fac0
    a1i
    eqtrd
    oveq1d
    @164
    c1
    c1
    cdiv
    co
    c1
    @56
    c1
    c1
    cdiv
    @8
    vt
    prod0
    oveq2i
    1div1e1
    eqtri
    syl6eq
    @58
    c1
    wceq
    @100
    @15
    vt
    prod0
    a1i
    oveq12d
    ad2antlr
    @163
    c1
    wceq
    @162
    1t1e1
    a1i
    eqtrd
    sumeq2dv
    @124
    c1
    wceq
    #
    @102
    @157
    c1
    cc
    wcel
    #
    @166
    0ex
    ax-1cn
    c1
    c1
    vc
    c0
    cvv
    @158
    c1
    eqidd
    sumsn
    mp2an
    a1i
    3eqtrd
    mpteq2dv
    eqcomd
    3eqtrd
    a1d
    wph
    @100
    wn
    #
    wa
    #
    @101
    @62
    @169
    @101
    wa
    #
    @53
    @22
    @104
    cfv
    #
    vx
    cX
    cc0
    cmpt
    @61
    @53
    @171
    wceq
    @170
    @22
    @52
    @104
    @106
    fveq1i
    a1i
    @170
    vx
    c1
    cS
    @22
    cX
    @169
    @111
    @101
    wph
    @111
    @168
    dvnprodlem3.s
    adantr
    adantr
    @169
    cX
    @121
    wcel
    #
    @101
    wph
    @172
    @168
    dvnprodlem3.x
    adantr
    adantr
    @167
    @170
    ax-1cn
    a1i
    @168
    @101
    @22
    cn
    wcel
    #
    wph
    @168
    @101
    wa
    #
    @22
    cn0
    wcel
    #
    @22
    cc0
    wne
    #
    wa
    @173
    @174
    @175
    @176
    @101
    @175
    @168
    @22
    cN
    elfznn0
    #
    adantl
    @168
    @176
    @101
    @22
    cc0
    neqne
    adantr
    jca
    @22
    elnnne0
    sylibr
    adantll
    dvnmptconst
    @170
    vx
    cX
    cc0
    @60
    @170
    @60
    c0
    @59
    vc
    csu
    #
    cc0
    @170
    @55
    c0
    @59
    vc
    @170
    vn
    @22
    @132
    c0
    cn0
    @54
    cvv
    wph
    @54
    @139
    wceq
    @168
    @101
    @151
    ad2antrr
    @169
    @130
    @22
    wceq
    #
    @132
    c0
    wceq
    #
    @101
    @168
    @179
    @180
    wph
    @168
    @179
    wa
    @132
    @127
    @22
    wceq
    #
    vc
    @123
    crab
    #
    c0
    @179
    @132
    @182
    wceq
    @168
    @179
    @131
    @181
    vc
    @123
    @130
    @22
    @127
    eqeq2
    rabbidv
    adantl
    @168
    @182
    c0
    wceq
    #
    @179
    @168
    @181
    wn
    #
    vc
    @123
    wral
    @183
    @168
    @184
    vc
    @123
    @168
    @161
    wa
    @181
    @100
    @161
    @181
    @100
    @168
    @181
    @100
    @161
    @181
    @22
    @22
    @127
    cc0
    @181
    @22
    eqidd
    @181
    @127
    @22
    @181
    id
    eqcomd
    @128
    @181
    @159
    a1i
    3eqtrd
    adantl
    adantll
    @168
    @161
    @181
    simpll
    pm2.65da
    ralrimiva
    @181
    vc
    @123
    rabeq0
    sylibr
    adantr
    eqtrd
    adantll
    adantlr
    @101
    @175
    @169
    @177
    adantl
    @157
    @170
    0ex
    a1i
    fvmptd
    sumeq1d
    @178
    cc0
    wceq
    @170
    @59
    vc
    sum0
    a1i
    eqtr2d
    mpteq2dv
    3eqtrd
    ex
    pm2.61dan
    ralrimiv
    wph
    @63
    cT
    wss
    #
    @78
    cT
    @63
    cdif
    wcel
    #
    wa
    #
    wa
    #
    @77
    @93
    @188
    @77
    wa
    #
    vj
    cv
    #
    @82
    cfv
    #
    vx
    cX
    @190
    @84
    cfv
    #
    @190
    cfa
    cfv
    #
    @86
    cdiv
    co
    #
    @88
    cmul
    co
    #
    vc
    csu
    #
    cmpt
    #
    wceq
    #
    vj
    @31
    wral
    @93
    @189
    @198
    vj
    @31
    @189
    @190
    @31
    wcel
    #
    wa
    @188
    @22
    cS
    vy
    cX
    @63
    vy
    cv
    #
    vu
    cv
    #
    cH
    cfv
    #
    cfv
    #
    vu
    cprod
    #
    cmpt
    #
    cdvn
    co
    #
    cfv
    #
    vy
    cX
    @69
    @25
    @63
    @201
    vd
    cv
    #
    cfv
    #
    cfa
    cfv
    #
    vu
    cprod
    #
    cdiv
    co
    #
    @63
    @200
    @209
    cS
    @202
    cdvn
    co
    #
    cfv
    #
    cfv
    #
    vu
    cprod
    #
    cmul
    co
    #
    vd
    csu
    #
    cmpt
    #
    wceq
    #
    vk
    @31
    wral
    #
    @199
    @198
    @188
    @77
    @199
    simpll
    @77
    @221
    @188
    @199
    @77
    @221
    @76
    @220
    vk
    @31
    @67
    @207
    @75
    @219
    @22
    @66
    @206
    @65
    @205
    cS
    cdvn
    vx
    vy
    cX
    @64
    @204
    @11
    @200
    wceq
    #
    @64
    @63
    @200
    @12
    cfv
    #
    vt
    cprod
    #
    @204
    @222
    @63
    @36
    @223
    vt
    @11
    @200
    @12
    fveq2
    prodeq2ad
    @224
    @204
    wceq
    @222
    @63
    @223
    @203
    vt
    vu
    @5
    @201
    wceq
    #
    @200
    @12
    @202
    @5
    @201
    cH
    fveq2
    #
    fveq1d
    cbvprodv
    a1i
    eqtrd
    cbvmptv
    oveq2i
    #
    fveq1i
    vx
    vy
    cX
    @74
    @218
    @222
    @74
    @69
    @25
    @63
    @201
    @6
    cfv
    #
    cfa
    cfv
    #
    vu
    cprod
    #
    cdiv
    co
    #
    @63
    @200
    @228
    @213
    cfv
    #
    cfv
    #
    vu
    cprod
    #
    cmul
    co
    #
    vc
    csu
    #
    @218
    @222
    @69
    @73
    @235
    vc
    @222
    @71
    @231
    @72
    @234
    cmul
    @71
    @231
    wceq
    @222
    @70
    @230
    @25
    cdiv
    @63
    @8
    @229
    vt
    vu
    @225
    @7
    @228
    cfa
    @5
    @201
    @6
    fveq2
    #
    fveq2d
    cbvprodv
    oveq2i
    a1i
    @222
    @72
    @63
    @200
    @14
    cfv
    #
    vt
    cprod
    #
    @234
    @222
    @63
    @15
    @238
    vt
    @11
    @200
    @14
    fveq2
    prodeq2ad
    @239
    @234
    wceq
    @222
    @63
    @238
    @233
    vt
    vu
    @225
    @200
    @14
    @232
    @225
    @7
    @228
    @13
    @213
    @225
    @12
    @202
    cS
    cdvn
    @226
    oveq2d
    @237
    fveq12d
    fveq1d
    cbvprodv
    a1i
    eqtrd
    oveq12d
    sumeq2ad
    @236
    @218
    wceq
    @222
    @69
    @235
    @217
    vc
    vd
    @6
    @208
    wceq
    #
    @231
    @212
    @234
    @216
    cmul
    @240
    @230
    @211
    @25
    cdiv
    @240
    @63
    @229
    @210
    vu
    @240
    @228
    @209
    cfa
    @201
    @6
    @208
    fveq1
    #
    fveq2d
    prodeq2ad
    oveq2d
    @240
    @63
    @233
    @215
    vu
    @240
    @200
    @232
    @214
    @240
    @228
    @209
    @213
    @241
    fveq2d
    fveq1d
    prodeq2ad
    oveq12d
    cbvsumv
    a1i
    eqtrd
    cbvmptv
    #
    eqeq12i
    ralbii
    biimpi
    ad2antlr
    @189
    @199
    simpr
    @188
    @221
    wa
    #
    @199
    wa
    #
    vx
    vt
    cD
    vd
    @192
    @190
    @78
    @208
    cfv
    #
    cmin
    co
    #
    @208
    @63
    cres
    #
    cop
    #
    cmpt
    @63
    cS
    cT
    vh
    vl
    vn
    cH
    @190
    cN
    cX
    @78
    vs
    vc
    wph
    @111
    @187
    @221
    @199
    dvnprodlem3.s
    ad3antrrr
    wph
    @172
    @187
    @221
    @199
    dvnprodlem3.x
    ad3antrrr
    wph
    cT
    cfn
    wcel
    #
    @187
    @221
    @199
    dvnprodlem3.t
    ad3antrrr
    @244
    @5
    cT
    wcel
    #
    wa
    wph
    @250
    cX
    cc
    @12
    wf
    wph
    @187
    @221
    @199
    @250
    simp-4l
    @244
    @250
    simpr
    dvnprodlem3.h
    syl2anc
    wph
    cN
    cn0
    wcel
    @187
    @221
    @199
    dvnprodlem3.n
    ad3antrrr
    @244
    @250
    vh
    cv
    #
    @31
    wcel
    #
    w3a
    wph
    @250
    @252
    cX
    cc
    @251
    @13
    cfv
    #
    wf
    #
    @244
    @250
    wph
    @252
    wph
    @187
    @221
    @199
    simplll
    3ad2ant1
    @244
    @250
    @252
    simp2
    @244
    @250
    @252
    simp3
    wph
    @250
    @199
    w3a
    #
    cX
    cc
    @190
    @13
    cfv
    #
    wf
    #
    wi
    wph
    @250
    @252
    w3a
    #
    @254
    wi
    vj
    vh
    @190
    @251
    wceq
    #
    @255
    @258
    @257
    @254
    @259
    @199
    @252
    wph
    @250
    @190
    @251
    @31
    eleq1
    3anbi3d
    @259
    cX
    cc
    @256
    @253
    @190
    @251
    @13
    fveq2
    feq1d
    imbi12d
    dvnprodlem3.dvnh
    chvarv
    syl3anc
    dvnprodlem3.d
    @188
    @185
    @221
    @199
    wph
    @185
    @186
    simprl
    ad2antrr
    @188
    @186
    @221
    @199
    wph
    @185
    @186
    simprr
    ad2antrr
    @221
    vl
    cv
    #
    @66
    cfv
    #
    vx
    cX
    @260
    @68
    cfv
    #
    @260
    cfa
    cfv
    #
    @70
    cdiv
    co
    #
    @72
    cmul
    co
    #
    vc
    csu
    #
    cmpt
    #
    wceq
    #
    vl
    @31
    wral
    #
    @188
    @199
    @221
    @269
    @220
    @268
    vk
    vl
    @31
    @22
    @260
    wceq
    #
    @207
    @261
    @219
    @267
    @270
    @22
    @260
    @206
    @66
    @206
    @66
    wceq
    @270
    @66
    @206
    @227
    eqcomi
    a1i
    @270
    id
    fveq12d
    @270
    @219
    @75
    @267
    @219
    @75
    wceq
    @270
    @75
    @219
    @242
    eqcomi
    a1i
    @270
    vx
    cX
    @74
    @266
    @270
    @74
    @69
    @265
    vc
    csu
    @266
    @270
    @69
    @73
    @265
    vc
    @270
    @71
    @264
    @72
    cmul
    @270
    @25
    @263
    @70
    cdiv
    @22
    @260
    cfa
    fveq2
    oveq1d
    oveq1d
    sumeq2ad
    @270
    @69
    @262
    @265
    vc
    @22
    @260
    @68
    fveq2
    sumeq1d
    eqtrd
    mpteq2dv
    eqtrd
    eqeq12d
    cbvralv
    biimpi
    ad2antlr
    @243
    @199
    simpr
    vd
    vc
    @192
    @248
    @190
    @78
    @6
    cfv
    #
    cmin
    co
    #
    @6
    @63
    cres
    #
    cop
    @208
    @6
    wceq
    #
    @246
    @272
    @247
    @273
    @274
    @245
    @271
    @190
    cmin
    @78
    @208
    @6
    fveq1
    oveq2d
    @208
    @6
    @63
    reseq1
    opeq12d
    cbvmptv
    dvnprodlem2
    syl21anc
    ralrimiva
    @198
    @92
    vj
    vk
    @31
    @190
    @22
    wceq
    #
    @191
    @83
    @197
    @91
    @190
    @22
    @82
    fveq2
    @275
    vx
    cX
    @196
    @90
    @275
    @196
    @192
    @89
    vc
    csu
    @90
    @275
    @192
    @195
    @89
    vc
    @275
    @194
    @87
    @88
    cmul
    @275
    @193
    @25
    @86
    cdiv
    @190
    @22
    cfa
    fveq2
    oveq1d
    oveq1d
    sumeq2ad
    @275
    @192
    @85
    @89
    vc
    @190
    @22
    @84
    fveq2
    sumeq1d
    eqtrd
    mpteq2dv
    eqeq12d
    cbvralv
    sylib
    ex
    dvnprodlem3.t
    findcard2d
    wph
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @33
    wph
    cN
    cn0
    @276
    dvnprodlem3.n
    nn0uz
    syl6eleq
    cc0
    cN
    eluzfz2
    syl
    @30
    @34
    vk
    cN
    @31
    @22
    cN
    wceq
    #
    @23
    @1
    @29
    @19
    @22
    cN
    @0
    fveq2
    @277
    vx
    cX
    @28
    @18
    @277
    @28
    @3
    @27
    vc
    csu
    @18
    @277
    @24
    @3
    @27
    vc
    @22
    cN
    @2
    fveq2
    sumeq1d
    @277
    @3
    @27
    @17
    vc
    @277
    @26
    @10
    @16
    cmul
    @277
    @25
    @4
    @9
    cdiv
    @22
    cN
    cfa
    fveq2
    oveq1d
    oveq1d
    sumeq2ad
    eqtrd
    mpteq2dv
    eqeq12d
    rspccva
    syl2anc
    wph
    vx
    cX
    @18
    @21
    wph
    @3
    @20
    @17
    vc
    wph
    cN
    @2
    cC
    wph
    @2
    vn
    cn0
    cT
    @7
    vt
    csu
    #
    @130
    wceq
    #
    vc
    @135
    cT
    cmap
    co
    #
    crab
    #
    cmpt
    #
    cC
    wph
    vs
    cT
    @138
    @282
    @140
    cD
    cvv
    @141
    @97
    @138
    @282
    wceq
    wph
    @97
    vn
    cn0
    @137
    @281
    @97
    @137
    @134
    vc
    @280
    crab
    #
    @281
    @97
    @136
    @280
    wceq
    @137
    @283
    wceq
    @35
    cT
    @135
    cmap
    oveq2
    @134
    vc
    @136
    @280
    rabeq
    syl
    @97
    @134
    @279
    vc
    @280
    @97
    @133
    @278
    @130
    @35
    cT
    @7
    vt
    sumeq1
    eqeq1d
    rabbidv
    eqtrd
    mpteq2dv
    adantl
    wph
    @249
    cT
    @140
    wcel
    dvnprodlem3.t
    cT
    cfn
    pwidg
    syl
    @282
    cvv
    wcel
    wph
    vn
    cn0
    @281
    nn0ex
    mptex
    a1i
    fvmptd
    cC
    @282
    wceq
    wph
    dvnprodlem3.c
    a1i
    eqtr4d
    fveq1d
    sumeq1d
    mpteq2dv
    eqtrd
end
