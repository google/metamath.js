include "cv.mm"
include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cflim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "wcel.mm"
include "wex.mm"
include "eldmg.mm"
include "ibi.mm"
include "syl.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "ctopon.mm"
include "cxmt.mm"
include "cme.mm"
include "metxmet.mm"
include "mopntopon.mm"
include "lmcl.mm"
include "sylan.mm"
include "cbl.mm"
include "wss.mm"
include "crp.mm"
include "wrex.mm"
include "adantr.mm"
include "mopni2.mm"
include "3expia.mm"
include "cfil.mm"
include "ad3antrrr.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "cexp.mm"
include "clt.mm"
include "cuz.mm"
include "cz.mm"
include "ad2antrr.mm"
include "rphalfcl.mm"
include "adantl.mm"
include "iscmet3lem3.mm"
include "syl2anc.mm"
include "blcntr.mm"
include "syl3anc.mm"
include "simplr.mm"
include "cxr.mm"
include "rpxrd.mm"
include "blopn.mm"
include "lmcvg.mm"
include "rexanuz2.mm"
include "r19.2uz.mm"
include "wf.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "ad2antrl.mm"
include "ffvelrn.mm"
include "rpxr.mm"
include "blssm.mm"
include "cle.mm"
include "cr.mm"
include "1rp.mm"
include "ax-mp.mm"
include "rpexpcl.mm"
include "mpan.mm"
include "rpred.mm"
include "ltle.mm"
include "simpll.mm"
include "cfz.mm"
include "eluzfz2.mm"
include "r19.21bi.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspcv.mm"
include "sylc.mm"
include "simpr.mm"
include "ad2antlr.mm"
include "rsp.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq1d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "wb.mm"
include "ffvelrnda.mm"
include "syl2an.mm"
include "filelss.mm"
include "sselda.mm"
include "elbl2.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "ex.mm"
include "ssrdv.mm"
include "ssbl.mm"
include "sstr.mm"
include "syl6an.mm"
include "syld.mm"
include "adantrd.mm"
include "impr.mm"
include "blcom.mm"
include "rpre.mm"
include "blhalf.mm"
include "expr.mm"
include "sylbid.mm"
include "adantld.mm"
include "sstrd.mm"
include "filss.mm"
include "syl13anc.mm"
include "rexlimdvaa.mm"
include "syl5.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "ad2ant2r.mm"
include "toponss.mm"
include "simprr.mm"
include "ralrimiva.mm"
include "flimopn.mm"
include "mpbir2and.mm"
include "ne0i.mm"
include "exlimddv.mm"

theorem iscmet3lem2
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cD: class D
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cJ: class J
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  assume iscmet3.1: |- Z = ( ZZ>= ` M )
  assume iscmet3.2: |- J = ( MetOpen ` D )
  assume iscmet3.3: |- ( ph -> M e. ZZ )
  assume iscmet3.4: |- ( ph -> D e. ( Met ` X ) )
  assume iscmet3.6: |- ( ph -> F : Z --> X )
  assume iscmet3.9: |- ( ph -> A. k e. ZZ A. u e. ( S ` k ) A. v e. ( S ` k ) ( u D v ) < ( ( 1 / 2 ) ^ k ) )
  assume iscmet3.10: |- ( ph -> A. k e. Z A. n e. ( M ... k ) ( F ` k ) e. ( S ` n ) )
  assume iscmet3.7: |- ( ph -> G e. ( Fil ` X ) )
  assume iscmet3.8: |- ( ph -> S : ZZ --> G )
  assume iscmet3.5: |- ( ph -> F e. dom ( ~~>t ` J ) )

  disjoint k n
  disjoint k u
  disjoint k v
  disjoint D k
  disjoint n u
  disjoint n v
  disjoint D n
  disjoint u v
  disjoint D u
  disjoint D v
  disjoint G k
  disjoint F k
  disjoint F n
  disjoint F u
  disjoint F v
  disjoint X k
  disjoint X n
  disjoint J k
  disjoint J n
  disjoint S k
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint Z k
  disjoint Z n
  disjoint M k
  disjoint M n
  disjoint k ph
  disjoint n ph
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint D f
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint D g
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i r
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint i y
  disjoint D i
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint j y
  disjoint D j
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k x
  disjoint k y
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint n y
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint D r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint D s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint D t
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint G j
  disjoint G r
  disjoint G x
  disjoint G y
  disjoint R j
  disjoint R k
  disjoint F j
  disjoint F r
  disjoint F x
  disjoint F y
  disjoint X f
  disjoint X g
  disjoint X i
  disjoint X j
  disjoint X r
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint J f
  disjoint J g
  disjoint J i
  disjoint J j
  disjoint J r
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint S y
  disjoint Z f
  disjoint Z g
  disjoint Z i
  disjoint Z j
  disjoint Z r
  disjoint Z s
  disjoint Z y
  disjoint M f
  disjoint M i
  disjoint M j
  disjoint M x
  disjoint f ph
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint ph r
  disjoint ph s
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( J fLim G ) =/= (/) )

  proof
    wph
    cF
    vx
    cv
    #
    cJ
    clm
    cfv
    #
    wbr
    #
    cJ
    cG
    cflim
    co
    #
    c0
    wne
    #
    vx
    wph
    cF
    @1
    cdm
    #
    wcel
    #
    @2
    vx
    wex
    #
    iscmet3.5
    @6
    @7
    vx
    cF
    @1
    @5
    eldmg
    ibi
    syl
    wph
    @2
    wa
    #
    @0
    @3
    wcel
    #
    @4
    @8
    @9
    @0
    cX
    wcel
    #
    @0
    vy
    cv
    #
    wcel
    #
    @11
    cG
    wcel
    #
    wi
    #
    vy
    cJ
    wral
    #
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @2
    @10
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @16
    wph
    cD
    cX
    cme
    cfv
    wcel
    @17
    iscmet3.4
    cD
    cX
    metxmet
    syl
    #
    cD
    cJ
    cX
    iscmet3.2
    mopntopon
    syl
    #
    @0
    cF
    cJ
    cX
    lmcl
    sylan
    #
    @8
    @14
    vy
    cJ
    @8
    @11
    cJ
    wcel
    #
    wa
    #
    @12
    @0
    vr
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    @11
    wss
    #
    vr
    crp
    wrex
    #
    @13
    @8
    @17
    @21
    @12
    @27
    wi
    wph
    @17
    @2
    @18
    adantr
    #
    @17
    @21
    @12
    @27
    vr
    @11
    cD
    @0
    cJ
    cX
    iscmet3.2
    mopni2
    3expia
    sylan
    @22
    @26
    @13
    vr
    crp
    @22
    @23
    crp
    wcel
    #
    @26
    wa
    #
    wa
    cG
    cX
    cfil
    cfv
    wcel
    #
    @25
    cG
    wcel
    #
    @11
    cX
    wss
    #
    @26
    @13
    wph
    @31
    @2
    @21
    @30
    iscmet3.7
    ad3antrrr
    @8
    @29
    @32
    @21
    @26
    @8
    @29
    wa
    #
    c1
    c2
    cdiv
    co
    #
    vk
    cv
    #
    cexp
    co
    #
    @23
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    vk
    vj
    cv
    cuz
    cfv
    #
    wral
    vj
    cZ
    wrex
    #
    @36
    cF
    cfv
    #
    @0
    @38
    @24
    co
    #
    wcel
    #
    vk
    @40
    wral
    vj
    cZ
    wrex
    #
    @32
    @34
    cM
    cz
    wcel
    #
    @38
    crp
    wcel
    #
    @41
    wph
    @46
    @2
    @29
    iscmet3.3
    ad2antrr
    #
    @29
    @47
    @8
    @23
    rphalfcl
    adantl
    #
    @38
    vj
    vk
    cM
    cZ
    iscmet3.1
    iscmet3lem3
    syl2anc
    @34
    @0
    @43
    vj
    vk
    cF
    cJ
    cM
    cZ
    iscmet3.1
    @34
    @17
    @10
    @47
    @0
    @43
    wcel
    @8
    @17
    @29
    @28
    adantr
    #
    @8
    @10
    @29
    @20
    adantr
    #
    @49
    cD
    @0
    @38
    cX
    blcntr
    syl3anc
    @48
    wph
    @2
    @29
    simplr
    @34
    @17
    @10
    @38
    cxr
    wcel
    #
    @43
    cJ
    wcel
    @50
    @51
    @34
    @38
    @49
    rpxrd
    #
    cD
    @0
    @38
    cJ
    cX
    iscmet3.2
    blopn
    syl3anc
    lmcvg
    @41
    @45
    wa
    @39
    @44
    wa
    #
    vk
    @40
    wral
    vj
    cZ
    wrex
    #
    @34
    @32
    @39
    @44
    vj
    vk
    cM
    cZ
    iscmet3.1
    rexanuz2
    @55
    @54
    vk
    cZ
    wrex
    @34
    @32
    @54
    vj
    vk
    cM
    cZ
    iscmet3.1
    r19.2uz
    @34
    @54
    @32
    vk
    cZ
    @34
    @36
    cZ
    wcel
    #
    @54
    wa
    #
    wa
    #
    @31
    @36
    cS
    cfv
    #
    cG
    wcel
    #
    @25
    cX
    wss
    #
    @59
    @25
    wss
    @32
    wph
    @31
    @2
    @29
    @57
    iscmet3.7
    ad3antrrr
    @58
    cz
    cG
    cS
    wf
    #
    @36
    cz
    wcel
    #
    @60
    wph
    @62
    @2
    @29
    @57
    iscmet3.8
    ad3antrrr
    @56
    @63
    @34
    @54
    @63
    @36
    cM
    cuz
    cfv
    #
    cZ
    cM
    @36
    eluzelz
    iscmet3.1
    eleq2s
    #
    ad2antrl
    cz
    cG
    @36
    cS
    ffvelrn
    #
    syl2anc
    @34
    @61
    @57
    @34
    @17
    @10
    @23
    cxr
    wcel
    #
    @61
    @50
    @51
    @29
    @67
    @8
    @23
    rpxr
    adantl
    cD
    @0
    @23
    cX
    blssm
    syl3anc
    adantr
    @58
    @59
    @42
    @38
    @24
    co
    #
    @25
    @34
    @56
    @54
    @59
    @68
    wss
    #
    @34
    @56
    wa
    #
    @39
    @69
    @44
    @70
    @39
    @37
    @38
    cle
    wbr
    #
    @69
    @70
    @37
    cr
    wcel
    @38
    cr
    wcel
    @39
    @71
    wi
    @70
    @37
    @70
    @63
    @37
    crp
    wcel
    #
    @56
    @63
    @34
    @65
    adantl
    @35
    crp
    wcel
    #
    @63
    @72
    c1
    crp
    wcel
    @73
    1rp
    c1
    rphalfcl
    ax-mp
    @35
    @36
    rpexpcl
    mpan
    #
    syl
    #
    rpred
    @70
    @38
    @34
    @47
    @56
    @49
    adantr
    rpred
    @37
    @38
    ltle
    syl2anc
    @70
    @59
    @42
    @37
    @24
    co
    #
    wss
    #
    @71
    @76
    @68
    wss
    #
    @69
    @34
    wph
    @56
    @77
    wph
    @2
    @29
    simpll
    wph
    @56
    wa
    #
    vy
    @59
    @76
    @79
    @11
    @59
    wcel
    #
    @11
    @76
    wcel
    #
    @79
    @80
    wa
    #
    @81
    @42
    @11
    cD
    co
    #
    @37
    clt
    wbr
    #
    @82
    @42
    @59
    wcel
    #
    @80
    vu
    cv
    #
    vv
    cv
    #
    cD
    co
    #
    @37
    clt
    wbr
    #
    vv
    @59
    wral
    vu
    @59
    wral
    #
    @84
    @79
    @85
    @80
    @79
    @36
    cM
    @36
    cfz
    co
    #
    wcel
    #
    @42
    vn
    cv
    #
    cS
    cfv
    #
    wcel
    #
    vn
    @91
    wral
    #
    @85
    @56
    @92
    wph
    @92
    @36
    @64
    cZ
    cM
    @36
    eluzfz2
    iscmet3.1
    eleq2s
    adantl
    wph
    @96
    vk
    cZ
    iscmet3.10
    r19.21bi
    @95
    @85
    vn
    @36
    @91
    vn
    vk
    weq
    @94
    @59
    @42
    @93
    @36
    cS
    fveq2
    eleq2d
    rspcv
    sylc
    adantr
    @79
    @80
    simpr
    @82
    @90
    vk
    cz
    wral
    #
    @63
    @90
    wph
    @97
    @56
    @80
    iscmet3.9
    ad2antrr
    @56
    @63
    wph
    @80
    @65
    ad2antlr
    @90
    vk
    cz
    rsp
    sylc
    @89
    @84
    @42
    @87
    cD
    co
    #
    @37
    clt
    wbr
    vu
    vv
    @42
    @11
    @59
    @59
    @86
    @42
    wceq
    @88
    @98
    @37
    clt
    @86
    @42
    @87
    cD
    oveq1
    breq1d
    vv
    vy
    weq
    @98
    @83
    @37
    clt
    @87
    @11
    @42
    cD
    oveq2
    breq1d
    rspc2va
    syl21anc
    @82
    @17
    @37
    cxr
    wcel
    #
    @42
    cX
    wcel
    #
    @11
    cX
    wcel
    @81
    @84
    wb
    wph
    @17
    @56
    @80
    @18
    ad2antrr
    @56
    @99
    wph
    @80
    @56
    @37
    @56
    @63
    @72
    @65
    @74
    syl
    rpxrd
    ad2antlr
    @79
    @100
    @80
    wph
    cZ
    cX
    @36
    cF
    iscmet3.6
    ffvelrnda
    adantr
    @79
    @59
    cX
    @11
    @79
    @31
    @60
    @59
    cX
    wss
    wph
    @31
    @56
    iscmet3.7
    adantr
    wph
    @62
    @63
    @60
    @56
    iscmet3.8
    @65
    @66
    syl2an
    @59
    cG
    cX
    filelss
    syl2anc
    sselda
    @11
    cD
    @42
    @37
    cX
    elbl2
    syl22anc
    mpbird
    ex
    ssrdv
    sylan
    @70
    @17
    @100
    @99
    @52
    @71
    @78
    wi
    @34
    @17
    @56
    @50
    adantr
    #
    @34
    cZ
    cX
    @36
    cF
    wph
    cZ
    cX
    cF
    wf
    @2
    @29
    iscmet3.6
    ad2antrr
    ffvelrnda
    #
    @70
    @37
    @75
    rpxrd
    @34
    @52
    @56
    @53
    adantr
    #
    @17
    @100
    wa
    #
    @99
    @52
    wa
    @71
    @78
    cD
    @42
    @37
    @38
    cX
    ssbl
    3expia
    syl22anc
    @59
    @76
    @68
    sstr
    syl6an
    syld
    adantrd
    impr
    @34
    @56
    @54
    @68
    @25
    wss
    #
    @70
    @44
    @105
    @39
    @70
    @44
    @0
    @68
    wcel
    #
    @105
    @70
    @17
    @52
    @10
    @100
    @44
    @106
    wb
    @101
    @103
    @34
    @10
    @56
    @51
    adantr
    @102
    @42
    cD
    @0
    @38
    cX
    blcom
    syl22anc
    @70
    @17
    @100
    @23
    cr
    wcel
    #
    @106
    @105
    wi
    @101
    @102
    @29
    @107
    @8
    @56
    @23
    rpre
    ad2antlr
    @104
    @107
    @106
    @105
    @23
    cD
    cX
    @42
    @0
    blhalf
    expr
    syl21anc
    sylbid
    adantld
    impr
    sstrd
    @59
    @25
    cG
    cX
    filss
    syl13anc
    rexlimdvaa
    syl5
    syl5bir
    mp2and
    ad2ant2r
    @22
    @33
    @30
    @8
    @16
    @21
    @33
    wph
    @16
    @2
    @19
    adantr
    @11
    cJ
    cX
    toponss
    sylan
    adantr
    @22
    @29
    @26
    simprr
    @25
    @11
    cG
    cX
    filss
    syl13anc
    rexlimdvaa
    syld
    ralrimiva
    wph
    @9
    @10
    @15
    wa
    wb
    #
    @2
    wph
    @16
    @31
    @108
    @19
    iscmet3.7
    vy
    @0
    cG
    cJ
    cX
    flimopn
    syl2anc
    adantr
    mpbir2and
    @3
    @0
    ne0i
    syl
    exlimddv
end
