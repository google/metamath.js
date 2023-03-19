include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "cr.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cmpt.mm"
include "wa.mm"
include "ccmp.mm"
include "wcel.mm"
include "adantr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "ccn.mm"
include "cc.mm"
include "cc0.mm"
include "ctop.mm"
include "ctopon.mm"
include "cmptop.mm"
include "syl.mm"
include "toptopon.mm"
include "sylib.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "1cnd.mm"
include "cnmptc.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cioo.mm"
include "ctg.mm"
include "cuni.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "cnf.mm"
include "frn.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "bndth.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "3jca.mm"
include "suprcl.mm"
include "recnd.mm"
include "feqmptd.mm"
include "cnfldtop.mm"
include "cnrest2r.mm"
include "ax-mp.mm"
include "tgioo2.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "sseldi.mm"
include "eqeltrrd.mm"
include "ctx.mm"
include "subcn.mm"
include "cnmpt12f.mm"
include "ad2antrr.mm"
include "ffvelrn.mm"
include "adantll.mm"
include "eldifsn.mm"
include "simpld.mm"
include "resubcld.mm"
include "simprd.mm"
include "necomd.mm"
include "subne0d.mm"
include "sylanbrc.mm"
include "fmptd.mm"
include "difssd.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "divcn.mm"
include "rereccld.mm"
include "ax-resscn.mm"
include "syl6eleqr.mm"
include "cif.mm"
include "simpr.mm"
include "1re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "0red.mm"
include "0lt1.mm"
include "max1.mm"
include "sylancr.mm"
include "ltletrd.mm"
include "gt0ne0d.mm"
include "recgt0d.mm"
include "elrpd.mm"
include "ltsubrpd.mm"
include "ltnled.mm"
include "wi.mm"
include "simprl.mm"
include "max2.mm"
include "ad2ant2l.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "suprub.mm"
include "syl2anc.mm"
include "ad2ant2rl.mm"
include "ltlend.mm"
include "mpbir2and.mm"
include "posdifd.mm"
include "letr.mm"
include "mpan2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "breq1d.mm"
include "ad2antll.mm"
include "adantrr.mm"
include "lerec.mm"
include "syl22anc.mm"
include "lesub.mm"
include "recrecd.mm"
include "breq2d.mm"
include "3bitr3d.mm"
include "3imtr4d.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "suprleub.mm"
include "bitrd.mm"
include "sylibrd.mm"
include "mtod.mm"
include "nrexdv.mm"
include "pm2.65da.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "ffvelrnda.mm"
include "baib.mm"
include "ffnfv.mm"
include "dfrex2.mm"
include "sylibr.mm"

theorem evth
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let vw: setvar w
  assume bndth.1: |- X = U. J
  assume bndth.2: |- K = ( topGen ` ran (,) )
  assume bndth.3: |- ( ph -> J e. Comp )
  assume bndth.4: |- ( ph -> F e. ( J Cn K ) )
  assume evth.5: |- ( ph -> X =/= (/) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint J x
  disjoint J y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint K u
  disjoint K v
  disjoint K z
  disjoint u w
  disjoint ph u
  disjoint v w
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint ph z
  disjoint X v
  disjoint X z
  disjoint J z
  assert |- ( ph -> E. x e. X A. y e. X ( F ` y ) <_ ( F ` x ) )

  proof
    wph
    vy
    cv
    #
    cF
    cfv
    #
    vx
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vy
    cX
    wral
    #
    wn
    #
    vx
    cX
    wral
    #
    wn
    @5
    vx
    cX
    wrex
    wph
    @7
    cX
    cr
    cF
    crn
    #
    cr
    clt
    csup
    #
    csn
    cdif
    #
    cF
    wf
    #
    wph
    @11
    @0
    vz
    cX
    c1
    @9
    vz
    cv
    #
    cF
    cfv
    #
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cfv
    #
    @2
    cle
    wbr
    #
    vy
    cX
    wral
    #
    vx
    cr
    wrex
    wph
    @11
    wa
    #
    vx
    vy
    @16
    cJ
    cK
    cX
    bndth.1
    bndth.2
    wph
    cJ
    ccmp
    wcel
    #
    @11
    bndth.3
    adantr
    #
    @20
    @16
    cJ
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    ccn
    co
    #
    cJ
    cK
    ccn
    co
    #
    @20
    @16
    cJ
    @23
    ccn
    co
    #
    wcel
    #
    @16
    @25
    wcel
    #
    @20
    vz
    c1
    @14
    cdiv
    cJ
    @23
    @23
    cc
    cc0
    csn
    #
    cdif
    #
    crest
    co
    #
    @23
    cX
    @20
    cJ
    ctop
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    @20
    @21
    @33
    @22
    cJ
    cmptop
    syl
    cJ
    cX
    bndth.1
    toptopon
    sylib
    #
    @20
    vz
    c1
    cJ
    @23
    cX
    cc
    @34
    @23
    cc
    ctopon
    cfv
    wcel
    #
    @20
    @23
    @23
    eqid
    #
    cnfldtopon
    a1i
    #
    @20
    1cnd
    cnmptc
    @20
    vz
    cX
    @14
    cmpt
    #
    @27
    wcel
    #
    @38
    cJ
    @32
    ccn
    co
    wcel
    #
    @20
    vz
    @9
    @13
    cmin
    cJ
    @23
    @23
    @23
    cX
    @34
    @20
    vz
    @9
    cJ
    @23
    cX
    cc
    @34
    @37
    wph
    @9
    cc
    wcel
    @11
    wph
    @9
    wph
    @8
    cr
    wss
    #
    @8
    c0
    wne
    #
    @12
    @2
    cle
    wbr
    #
    vz
    @8
    wral
    #
    vx
    cr
    wrex
    #
    w3a
    #
    @9
    cr
    wcel
    #
    wph
    @41
    @42
    @45
    wph
    cX
    cr
    cF
    wf
    #
    @41
    wph
    cF
    @26
    wcel
    @48
    bndth.4
    cF
    cJ
    cK
    cX
    cr
    bndth.1
    cr
    cioo
    crn
    ctg
    cfv
    #
    cuni
    cK
    cuni
    uniretop
    cK
    @49
    bndth.2
    unieqi
    eqtr4i
    cnf
    syl
    #
    cX
    cr
    cF
    frn
    syl
    wph
    cF
    cdm
    #
    c0
    wne
    @42
    wph
    @51
    cX
    c0
    wph
    @48
    @51
    cX
    wceq
    @50
    cX
    cr
    cF
    fdm
    syl
    evth.5
    eqnetrd
    @51
    c0
    @8
    c0
    cF
    dm0rn0
    necon3bii
    sylib
    wph
    @45
    @1
    @2
    cle
    wbr
    #
    vy
    cX
    wral
    #
    vx
    cr
    wrex
    wph
    vx
    vy
    cF
    cJ
    cK
    cX
    bndth.1
    bndth.2
    bndth.3
    bndth.4
    bndth
    wph
    @44
    @53
    vx
    cr
    wph
    cF
    cX
    wfn
    #
    @44
    @53
    wb
    wph
    @48
    @54
    @50
    cX
    cr
    cF
    ffn
    syl
    #
    @43
    @52
    vz
    vy
    cX
    cF
    @12
    @1
    @2
    cle
    breq1
    ralrn
    syl
    rexbidv
    mpbird
    3jca
    #
    vx
    vz
    @8
    suprcl
    syl
    #
    recnd
    adantr
    cnmptc
    wph
    vz
    cX
    @13
    cmpt
    #
    @27
    wcel
    @11
    wph
    cF
    @58
    @27
    wph
    vz
    cX
    cr
    cF
    @50
    feqmptd
    wph
    @25
    @27
    cF
    @23
    ctop
    wcel
    @25
    @27
    wss
    @23
    @36
    cnfldtop
    cr
    cJ
    @23
    cnrest2r
    ax-mp
    wph
    cF
    @26
    @25
    bndth.4
    cK
    @24
    cJ
    ccn
    cK
    @49
    @24
    bndth.2
    @23
    @36
    tgioo2
    eqtri
    oveq2i
    #
    syl6eleq
    sseldi
    eqeltrrd
    adantr
    cmin
    @23
    @23
    ctx
    co
    @23
    ccn
    co
    wcel
    @20
    @23
    @36
    subcn
    a1i
    cnmpt12f
    @20
    @35
    @38
    crn
    @31
    wss
    #
    @31
    cc
    wss
    @39
    @40
    wb
    @37
    @20
    cX
    @31
    @38
    wf
    @60
    @20
    vz
    cX
    @14
    @31
    @38
    @20
    @12
    cX
    wcel
    #
    wa
    #
    @14
    cc
    wcel
    @14
    cc0
    wne
    @14
    @31
    wcel
    @62
    @14
    @62
    @9
    @13
    wph
    @47
    @11
    @61
    @57
    ad2antrr
    #
    @62
    @13
    cr
    wcel
    #
    @13
    @9
    wne
    #
    @62
    @13
    @10
    wcel
    #
    @64
    @65
    wa
    @11
    @61
    @66
    wph
    cX
    @10
    @12
    cF
    ffvelrn
    adantll
    @13
    cr
    @9
    eldifsn
    sylib
    #
    simpld
    #
    resubcld
    #
    recnd
    @62
    @9
    @13
    @62
    @9
    @63
    recnd
    @62
    @13
    @68
    recnd
    @62
    @13
    @9
    @62
    @64
    @65
    @67
    simprd
    necomd
    subne0d
    #
    @14
    cc
    cc0
    eldifsn
    sylanbrc
    @38
    eqid
    fmptd
    cX
    @31
    @38
    frn
    syl
    @20
    cc
    @30
    difssd
    @31
    @38
    cJ
    @23
    cc
    cnrest2
    syl3anc
    mpbid
    cdiv
    @23
    @32
    ctx
    co
    @23
    ccn
    co
    wcel
    @20
    @23
    @32
    @36
    @32
    eqid
    divcn
    a1i
    cnmpt12f
    @20
    @35
    @16
    crn
    cr
    wss
    #
    cr
    cc
    wss
    #
    @28
    @29
    wb
    @37
    @20
    cX
    cr
    @16
    wf
    @71
    @20
    vz
    cX
    @15
    cr
    @16
    @62
    @14
    @69
    @70
    rereccld
    @16
    eqid
    #
    fmptd
    cX
    cr
    @16
    frn
    syl
    @72
    @20
    ax-resscn
    a1i
    cr
    @16
    cJ
    @23
    cc
    cnrest2
    syl3anc
    mpbid
    @59
    syl6eleqr
    bndth
    @20
    @19
    vx
    cr
    @20
    @2
    cr
    wcel
    #
    wa
    #
    @19
    @9
    @9
    c1
    c1
    @2
    cle
    wbr
    #
    @2
    c1
    cif
    #
    cdiv
    co
    #
    cmin
    co
    #
    cle
    wbr
    #
    @75
    @79
    @9
    clt
    wbr
    @80
    wn
    @75
    @9
    @78
    wph
    @47
    @11
    @74
    @57
    ad2antrr
    #
    @75
    @78
    @75
    @77
    @75
    @74
    c1
    cr
    wcel
    #
    @77
    cr
    wcel
    #
    @20
    @74
    simpr
    #
    1re
    @76
    @2
    c1
    cr
    ifcl
    #
    sylancl
    #
    @75
    @77
    @75
    cc0
    c1
    @77
    @75
    0red
    @82
    @75
    1re
    a1i
    @86
    cc0
    c1
    clt
    wbr
    @75
    0lt1
    a1i
    @75
    @82
    @74
    c1
    @77
    cle
    wbr
    1re
    @84
    c1
    @2
    max1
    sylancr
    ltletrd
    #
    gt0ne0d
    #
    rereccld
    #
    @75
    @77
    @86
    @87
    recgt0d
    elrpd
    ltsubrpd
    @75
    @79
    @9
    @75
    @9
    @78
    @81
    @89
    resubcld
    #
    @81
    ltnled
    mpbid
    @75
    @19
    @1
    @79
    cle
    wbr
    #
    vy
    cX
    wral
    #
    @80
    @75
    @18
    @91
    vy
    cX
    @20
    @74
    @0
    cX
    wcel
    #
    @18
    @91
    wi
    @20
    @74
    @93
    wa
    #
    wa
    #
    c1
    @9
    @1
    cmin
    co
    #
    cdiv
    co
    #
    @2
    cle
    wbr
    #
    @97
    @77
    cle
    wbr
    #
    @18
    @91
    @95
    @98
    @2
    @77
    cle
    wbr
    #
    @99
    @95
    @82
    @74
    @100
    1re
    @20
    @74
    @93
    simprl
    #
    c1
    @2
    max2
    sylancr
    @95
    @97
    cr
    wcel
    @74
    @83
    @98
    @100
    wa
    @99
    wi
    @95
    @96
    @95
    @9
    @1
    wph
    @47
    @11
    @94
    @57
    ad2antrr
    #
    @95
    @1
    cr
    wcel
    #
    @1
    @9
    wne
    #
    @95
    @1
    @10
    wcel
    #
    @103
    @104
    wa
    @11
    @93
    @105
    wph
    @74
    cX
    @10
    @0
    cF
    ffvelrn
    ad2ant2l
    @1
    cr
    @9
    eldifsn
    sylib
    #
    simpld
    #
    resubcld
    #
    @95
    @96
    @95
    @1
    @9
    clt
    wbr
    #
    cc0
    @96
    clt
    wbr
    #
    @95
    @109
    @1
    @9
    cle
    wbr
    #
    @9
    @1
    wne
    wph
    @93
    @111
    @11
    @74
    wph
    @93
    wa
    @46
    @1
    @8
    wcel
    #
    @111
    wph
    @46
    @93
    @56
    adantr
    wph
    @54
    @93
    @112
    @55
    cX
    @0
    cF
    fnfvelrn
    sylan
    vx
    vz
    @8
    @1
    suprub
    syl2anc
    #
    ad2ant2rl
    @95
    @1
    @9
    @95
    @103
    @104
    @106
    simprd
    necomd
    @95
    @1
    @9
    @107
    @102
    ltlend
    mpbir2and
    @95
    @1
    @9
    @107
    @102
    posdifd
    mpbid
    #
    gt0ne0d
    rereccld
    @101
    @95
    @74
    @82
    @83
    @101
    1re
    @85
    sylancl
    #
    @97
    @2
    @77
    letr
    syl3anc
    mpan2d
    @93
    @18
    @98
    wb
    @20
    @74
    @93
    @17
    @97
    @2
    cle
    vz
    @0
    @15
    @97
    cX
    @16
    @12
    @0
    wceq
    #
    @14
    @96
    c1
    cdiv
    @116
    @13
    @1
    @9
    cmin
    @12
    @0
    cF
    fveq2
    oveq2d
    oveq2d
    @73
    c1
    @96
    cdiv
    ovex
    fvmpt
    breq1d
    ad2antll
    @95
    @78
    @96
    cle
    wbr
    #
    @97
    c1
    @78
    cdiv
    co
    #
    cle
    wbr
    #
    @91
    @99
    @95
    @78
    cr
    wcel
    #
    cc0
    @78
    clt
    wbr
    @96
    cr
    wcel
    @110
    @117
    @119
    wb
    @20
    @74
    @120
    @93
    @89
    adantrr
    #
    @95
    @77
    @115
    @20
    @74
    cc0
    @77
    clt
    wbr
    @93
    @87
    adantrr
    recgt0d
    @108
    @114
    @78
    @96
    lerec
    syl22anc
    @95
    @120
    @47
    @103
    @117
    @91
    wb
    @121
    @102
    @107
    @78
    @9
    @1
    lesub
    syl3anc
    @95
    @118
    @77
    @97
    cle
    @95
    @77
    @95
    @77
    @115
    recnd
    @20
    @74
    @77
    cc0
    wne
    @93
    @88
    adantrr
    recrecd
    breq2d
    3bitr3d
    3imtr4d
    anassrs
    ralimdva
    @75
    @80
    @12
    @79
    cle
    wbr
    #
    vz
    @8
    wral
    #
    @92
    @75
    @46
    @79
    cr
    wcel
    @80
    @123
    wb
    wph
    @46
    @11
    @74
    @56
    ad2antrr
    @90
    vx
    vz
    vz
    @8
    @79
    suprleub
    syl2anc
    @75
    @54
    @123
    @92
    wb
    wph
    @54
    @11
    @74
    @55
    ad2antrr
    @122
    @91
    vz
    vy
    cX
    cF
    @12
    @1
    @79
    cle
    breq1
    ralrn
    syl
    bitrd
    sylibrd
    mtod
    nrexdv
    pm2.65da
    wph
    @7
    @3
    @10
    wcel
    #
    vx
    cX
    wral
    #
    @11
    wph
    @6
    @124
    vx
    cX
    wph
    @2
    cX
    wcel
    #
    wa
    #
    @6
    @3
    @9
    wne
    #
    @124
    wph
    @6
    @128
    wi
    @126
    wph
    @5
    @3
    @9
    wph
    @5
    @3
    @9
    wceq
    #
    @111
    vy
    cX
    wral
    wph
    @111
    vy
    cX
    @113
    ralrimiva
    @129
    @4
    @111
    vy
    cX
    @3
    @9
    @1
    cle
    breq2
    ralbidv
    syl5ibrcom
    necon3bd
    adantr
    @127
    @3
    cr
    wcel
    #
    @124
    @128
    wb
    wph
    cX
    cr
    @2
    cF
    @50
    ffvelrnda
    @124
    @130
    @128
    @3
    cr
    @9
    eldifsn
    baib
    syl
    sylibrd
    ralimdva
    wph
    @54
    @11
    @125
    wb
    @55
    @11
    @54
    @125
    vx
    cX
    @10
    cF
    ffnfv
    baib
    syl
    sylibrd
    mtod
    @5
    vx
    cX
    dfrex2
    sylibr
end
