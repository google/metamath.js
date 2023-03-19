include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cdv.mm"
include "co.mm"
include "wbr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cnt.mm"
include "csn.mm"
include "cdif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "wss.mm"
include "wral.mm"
include "cuz.mm"
include "cz.mm"
include "uzid.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "cdm.mm"
include "ulmdvlem2.mm"
include "cc.mm"
include "cr.mm"
include "cpr.mm"
include "recnprss.mm"
include "adantr.mm"
include "cmap.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "dvbsss.mm"
include "syl6eqssr.mm"
include "eqid.mm"
include "dvbssntr.mm"
include "eqsstr3d.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "biidd.mm"
include "rspcv.mm"
include "sylc.mm"
include "sselda.mm"
include "wne.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "crp.mm"
include "wrex.mm"
include "culm.mm"
include "ulmcl.mm"
include "c2.mm"
include "rphalfcl.mm"
include "adantl.mm"
include "wrel.mm"
include "ulmrel.mm"
include "releldm.mm"
include "sylancr.mm"
include "cvv.mm"
include "ulmscl.mm"
include "wfn.mm"
include "ovex.mm"
include "rgenw.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "ulmf2.mm"
include "syl2anc.mm"
include "ulmcau2.mm"
include "mpbid.mm"
include "uztrn2.mm"
include "ad2ant2lr.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "fvmpt.mm"
include "fveq1d.mm"
include "simprr.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "2ralbidva.mm"
include "rexbidva.mm"
include "ad2antrr.mm"
include "breq2.mm"
include "2ralbidv.mm"
include "rexralbidv.mm"
include "fvex.mm"
include "simplr.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "eqtr4d.mm"
include "ulmclm.mm"
include "climi2.mm"
include "rexanuz2.mm"
include "r19.2uz.mm"
include "sylbir.mm"
include "simpllr.mm"
include "eqeltrrd.mm"
include "fdm.mm"
include "3syl.mm"
include "eleqtrrd.mm"
include "wfun.mm"
include "wb.mm"
include "ad3antrrr.mm"
include "dvfg.mm"
include "ffun.mm"
include "funfvbrb.mm"
include "4syl.mm"
include "eldv.mm"
include "simprd.mm"
include "sstrd.mm"
include "dvlem.mm"
include "fmptd.mm"
include "ssdifssd.mm"
include "sseldd.mm"
include "ellimc3.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "id.mm"
include "breqan12rd.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "adantrr.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cbl.mm"
include "w3a.mm"
include "anass.mm"
include "df-3an.mm"
include "cli.mm"
include "mpteq2dv.mm"
include "breq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprr3.mm"
include "simplll.mm"
include "simpld.mm"
include "simpr3.mm"
include "simprr1.mm"
include "simprr2.mm"
include "simpr1.mm"
include "eldifad.mm"
include "simpr2.mm"
include "mpand.mm"
include "ulmdvlem1.mm"
include "anassrs.mm"
include "sylanb.mm"
include "sylan2br.mm"
include "3exp2.mm"
include "imp.mm"
include "sylibrd.mm"
include "ralimdva.mm"
include "impr.mm"
include "an32s.mm"
include "cxmt.mm"
include "cmopn.mm"
include "cnxmet.mm"
include "xmetres2.mm"
include "ctop.mm"
include "cuni.mm"
include "cnfldtop.mm"
include "resttop.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "ntrss2.mm"
include "eqssd.mm"
include "isopn3.mm"
include "mpbird.mm"
include "cnfldtopn.mm"
include "metrest.mm"
include "eleqtrd.mm"
include "simprl.mm"
include "mopni3.mm"
include "syl31anc.mm"
include "reximddv.mm"
include "rexlimddv.mm"
include "rexlimdvaa.mm"
include "syl5.mm"
include "mp2and.mm"
include "simpr.mm"
include "mpbir2and.mm"

theorem ulmdvlem3
  let wph: wff ph
  let vz: setvar z
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let cN: class N
  let cC: class C
  let wps: wff ps
  let cU: class U
  let cR: class R
  let cY: class Y
  assume ulmdv.z: |- Z = ( ZZ>= ` M )
  assume ulmdv.s: |- ( ph -> S e. { RR , CC } )
  assume ulmdv.m: |- ( ph -> M e. ZZ )
  assume ulmdv.f: |- ( ph -> F : Z --> ( CC ^m X ) )
  assume ulmdv.g: |- ( ph -> G : X --> CC )
  assume ulmdv.l: |- ( ( ph /\ z e. X ) -> ( k e. Z |-> ( ( F ` k ) ` z ) ) ~~> ( G ` z ) )
  assume ulmdv.u: |- ( ph -> ( k e. Z |-> ( S _D ( F ` k ) ) ) ( ~~>u ` X ) H )

  disjoint k z
  disjoint F k
  disjoint F z
  disjoint G z
  disjoint H z
  disjoint M k
  disjoint k ph
  disjoint ph z
  disjoint S k
  disjoint S z
  disjoint X k
  disjoint X z
  disjoint Z k
  disjoint Z z
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j s
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m s
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n s
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint n r
  disjoint G n
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r y
  disjoint r z
  disjoint G r
  disjoint G s
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint C k
  disjoint C n
  disjoint C y
  disjoint C z
  disjoint j r
  disjoint H j
  disjoint H n
  disjoint H r
  disjoint H s
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H y
  disjoint M j
  disjoint M n
  disjoint M x
  disjoint n ps
  disjoint ps w
  disjoint ps y
  disjoint j ph
  disjoint k r
  disjoint m r
  disjoint m ph
  disjoint n ph
  disjoint r x
  disjoint ph r
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint S j
  disjoint S m
  disjoint S n
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint U y
  disjoint R m
  disjoint R n
  disjoint R x
  disjoint R y
  disjoint X j
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X s
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint Y k
  disjoint Y n
  disjoint Y y
  disjoint Y z
  disjoint Z j
  disjoint Z m
  disjoint Z n
  disjoint Z s
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z x
  disjoint Z y
  assert |- ( ( ph /\ z e. X ) -> z ( S _D G ) ( H ` z ) )

  proof
    wph
    vz
    cv
    #
    cX
    wcel
    #
    wa
    #
    @0
    @0
    cH
    cfv
    #
    cS
    cG
    cdv
    co
    wbr
    @0
    cX
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    cnt
    cfv
    cfv
    #
    wcel
    #
    @3
    vy
    cX
    @0
    csn
    #
    cdif
    #
    vy
    cv
    #
    cG
    cfv
    #
    @0
    cG
    cfv
    #
    cmin
    co
    #
    @10
    @0
    cmin
    co
    #
    cdiv
    co
    #
    cmpt
    #
    @0
    climc
    co
    wcel
    #
    wph
    cX
    @6
    @0
    wph
    cM
    cZ
    wcel
    #
    cX
    @6
    wss
    #
    vk
    cZ
    wral
    @19
    wph
    cM
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    cz
    wcel
    #
    cM
    @20
    wcel
    ulmdv.m
    cM
    uzid
    syl
    ulmdv.z
    syl6eleqr
    #
    wph
    @19
    vk
    cZ
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    cX
    cS
    @23
    cF
    cfv
    #
    cdv
    co
    #
    cdm
    #
    @6
    wph
    vz
    cS
    vk
    cF
    cG
    cH
    cM
    cX
    cZ
    ulmdv.z
    ulmdv.s
    ulmdv.m
    ulmdv.f
    ulmdv.g
    ulmdv.l
    ulmdv.u
    ulmdvlem2
    #
    @25
    cX
    cS
    @26
    @5
    @4
    wph
    cS
    cc
    wss
    #
    @24
    wph
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    @30
    ulmdv.s
    cS
    recnprss
    #
    syl
    #
    adantr
    @25
    @26
    cc
    cX
    cmap
    co
    #
    wcel
    cX
    cc
    @26
    wf
    wph
    cZ
    @35
    @23
    cF
    ulmdv.f
    ffvelrnda
    @26
    cc
    cX
    elmapi
    syl
    @25
    cX
    @28
    cS
    @29
    cS
    @26
    dvbsss
    syl6eqssr
    #
    @5
    eqid
    #
    @4
    eqid
    #
    dvbssntr
    eqsstr3d
    ralrimiva
    @19
    @19
    vk
    cM
    cZ
    @23
    cM
    wceq
    #
    @19
    biidd
    rspcv
    sylc
    #
    sselda
    @2
    @17
    @3
    cc
    wcel
    vv
    cv
    #
    @0
    wne
    #
    @41
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    vu
    cv
    #
    clt
    wbr
    #
    wa
    #
    @41
    @16
    cfv
    #
    @3
    cmin
    co
    #
    cabs
    cfv
    #
    vr
    cv
    #
    clt
    wbr
    #
    wi
    #
    vv
    @9
    wral
    #
    vu
    crp
    wrex
    #
    vr
    crp
    wral
    wph
    cX
    cc
    @0
    cH
    wph
    vk
    cZ
    @27
    cmpt
    #
    cH
    cX
    culm
    cfv
    #
    wbr
    #
    cX
    cc
    cH
    wf
    ulmdv.u
    cX
    @56
    cH
    ulmcl
    syl
    ffvelrnda
    @2
    @55
    vr
    crp
    @2
    @51
    crp
    wcel
    #
    wa
    #
    vx
    cv
    #
    cS
    vn
    cv
    #
    cF
    cfv
    #
    cdv
    co
    #
    cfv
    #
    @61
    cS
    vm
    cv
    #
    cF
    cfv
    #
    cdv
    co
    #
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @51
    c2
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    vx
    cX
    wral
    vm
    @62
    cuz
    cfv
    #
    wral
    #
    vn
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    vj
    cZ
    wrex
    #
    @0
    @64
    cfv
    #
    @3
    cmin
    co
    cabs
    cfv
    @72
    clt
    wbr
    #
    vn
    @78
    wral
    vj
    cZ
    wrex
    #
    @55
    @60
    @73
    crp
    wcel
    #
    @71
    vs
    cv
    #
    clt
    wbr
    #
    vx
    cX
    wral
    #
    vm
    @75
    wral
    #
    vn
    @78
    wral
    #
    vj
    cZ
    wrex
    #
    vs
    crp
    wral
    #
    @79
    @60
    @72
    crp
    wcel
    #
    @83
    @59
    @91
    @2
    @51
    rphalfcl
    adantl
    #
    @72
    rphalfcl
    syl
    #
    wph
    @90
    @1
    @59
    wph
    @61
    @62
    @56
    cfv
    #
    cfv
    #
    @61
    @66
    @56
    cfv
    #
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @84
    clt
    wbr
    #
    vx
    cX
    wral
    #
    vm
    @75
    wral
    vn
    @78
    wral
    #
    vj
    cZ
    wrex
    #
    vs
    crp
    wral
    #
    @90
    wph
    @56
    @57
    cdm
    wcel
    #
    @104
    wph
    @57
    wrel
    @58
    @105
    cX
    ulmrel
    ulmdv.u
    @56
    cH
    @57
    releldm
    sylancr
    wph
    vs
    vx
    cX
    vj
    vn
    vm
    @56
    cM
    cvv
    cZ
    ulmdv.z
    ulmdv.m
    wph
    @58
    cX
    cvv
    wcel
    ulmdv.u
    cX
    @56
    cH
    ulmscl
    syl
    wph
    @56
    cZ
    wfn
    #
    @58
    cZ
    @35
    @56
    wf
    #
    @27
    cvv
    wcel
    #
    vk
    cZ
    wral
    @106
    wph
    @108
    vk
    cZ
    cS
    @26
    cdv
    ovex
    rgenw
    vk
    cZ
    @27
    @56
    cvv
    @56
    eqid
    #
    fnmpt
    mp1i
    ulmdv.u
    cX
    @56
    cH
    cZ
    ulmf2
    syl2anc
    #
    ulmcau2
    mpbid
    wph
    @103
    @89
    vs
    crp
    wph
    @102
    @88
    vj
    cZ
    wph
    @77
    cZ
    wcel
    #
    wa
    #
    @101
    @86
    vn
    vm
    @78
    @75
    @112
    @62
    @78
    wcel
    #
    @66
    @75
    wcel
    #
    wa
    wa
    #
    @100
    @85
    vx
    cX
    @115
    @99
    @71
    @84
    clt
    @115
    @98
    @70
    cabs
    @115
    @95
    @65
    @97
    @69
    cmin
    @115
    @61
    @94
    @64
    @115
    @62
    cZ
    wcel
    #
    @94
    @64
    wceq
    #
    @111
    @113
    @116
    wph
    @114
    cM
    @62
    @77
    cZ
    ulmdv.z
    uztrn2
    ad2ant2lr
    #
    vk
    @62
    @27
    @64
    cZ
    @56
    vk
    vn
    weq
    #
    @26
    @63
    cS
    cdv
    @23
    @62
    cF
    fveq2
    oveq2d
    #
    @109
    cS
    @63
    cdv
    ovex
    fvmpt
    #
    syl
    fveq1d
    @115
    @61
    @96
    @68
    @115
    @66
    cZ
    wcel
    #
    @96
    @68
    wceq
    @115
    @116
    @114
    @122
    @118
    @112
    @113
    @114
    simprr
    cM
    @66
    @62
    cZ
    ulmdv.z
    uztrn2
    syl2anc
    vk
    @66
    @27
    @68
    cZ
    @56
    vk
    vm
    weq
    @26
    @67
    cS
    cdv
    @23
    @66
    cF
    fveq2
    oveq2d
    @109
    cS
    @67
    cdv
    ovex
    fvmpt
    syl
    fveq1d
    oveq12d
    fveq2d
    breq1d
    ralbidv
    2ralbidva
    rexbidva
    ralbidv
    mpbid
    ad2antrr
    @89
    @79
    vs
    @73
    crp
    @84
    @73
    wceq
    #
    @87
    @76
    vj
    vn
    cZ
    @78
    @123
    @85
    @74
    vm
    vx
    @75
    cX
    @84
    @73
    @71
    clt
    breq2
    2ralbidv
    rexralbidv
    rspcv
    sylc
    @60
    @3
    @80
    @72
    vj
    vn
    vk
    cZ
    @0
    @27
    cfv
    #
    cmpt
    #
    cM
    cZ
    ulmdv.z
    wph
    @21
    @1
    @59
    ulmdv.m
    ad2antrr
    #
    @92
    @116
    @62
    @125
    cfv
    #
    @80
    wceq
    @60
    vk
    @62
    @124
    @80
    cZ
    @125
    @119
    @0
    @27
    @64
    @120
    fveq1d
    @125
    eqid
    @0
    @64
    fvex
    fvmpt
    adantl
    #
    @60
    @0
    cX
    vn
    @56
    cH
    @125
    cM
    cvv
    cZ
    ulmdv.z
    @126
    wph
    @107
    @1
    @59
    @110
    ad2antrr
    #
    wph
    @1
    @59
    simplr
    #
    @125
    cvv
    wcel
    @60
    vk
    cZ
    @124
    cZ
    @20
    cvv
    ulmdv.z
    cM
    cuz
    fvex
    eqeltri
    mptex
    a1i
    @60
    @116
    wa
    #
    @0
    @94
    cfv
    @80
    @127
    @131
    @0
    @94
    @64
    @116
    @117
    @60
    @121
    adantl
    #
    fveq1d
    @128
    eqtr4d
    wph
    @58
    @1
    @59
    ulmdv.u
    ad2antrr
    ulmclm
    climi2
    @79
    @82
    wa
    #
    @76
    @81
    wa
    #
    vn
    cZ
    wrex
    #
    @60
    @55
    @133
    @134
    vn
    @78
    wral
    vj
    cZ
    wrex
    @135
    @76
    @81
    vj
    vn
    cM
    cZ
    ulmdv.z
    rexanuz2
    @134
    vj
    vn
    cM
    cZ
    ulmdv.z
    r19.2uz
    sylbir
    @60
    @134
    @55
    vn
    cZ
    @60
    @116
    @134
    wa
    #
    wa
    #
    @42
    @44
    vw
    cv
    #
    clt
    wbr
    #
    wa
    #
    @41
    @63
    cfv
    #
    @0
    @63
    cfv
    #
    cmin
    co
    #
    @43
    cdiv
    co
    #
    @80
    cmin
    co
    #
    cabs
    cfv
    #
    @73
    clt
    wbr
    #
    wi
    #
    vv
    @9
    wral
    #
    @55
    vw
    crp
    @60
    @116
    @149
    vw
    crp
    wrex
    #
    @134
    @131
    @83
    @140
    @41
    vy
    @9
    @10
    @63
    cfv
    #
    @142
    cmin
    co
    #
    @14
    cdiv
    co
    #
    cmpt
    #
    cfv
    #
    @80
    cmin
    co
    #
    cabs
    cfv
    #
    @84
    clt
    wbr
    #
    wi
    #
    vv
    @9
    wral
    #
    vw
    crp
    wrex
    #
    vs
    crp
    wral
    #
    @150
    @60
    @83
    @116
    @93
    adantr
    @131
    @80
    cc
    wcel
    #
    @162
    @131
    @80
    @154
    @0
    climc
    co
    wcel
    #
    @163
    @162
    wa
    @131
    @7
    @164
    @131
    @0
    @80
    @64
    wbr
    #
    @7
    @164
    wa
    @131
    @0
    @64
    cdm
    #
    wcel
    #
    @165
    @131
    @0
    cX
    @166
    wph
    @1
    @59
    @116
    simpllr
    #
    @131
    @64
    @35
    wcel
    cX
    cc
    @64
    wf
    @166
    cX
    wceq
    @131
    @94
    @64
    @35
    @132
    @60
    cZ
    @35
    @62
    @56
    @129
    ffvelrnda
    eqeltrrd
    @64
    cc
    cX
    elmapi
    cX
    cc
    @64
    fdm
    3syl
    eleqtrrd
    @131
    @32
    @166
    cc
    @64
    wf
    @64
    wfun
    @167
    @165
    wb
    wph
    @32
    @1
    @59
    @116
    ulmdv.s
    ad3antrrr
    #
    cS
    @63
    dvfg
    @166
    cc
    @64
    ffun
    @0
    @64
    funfvbrb
    4syl
    mpbid
    @131
    vy
    cX
    @0
    @80
    cS
    @5
    @63
    @154
    @4
    @37
    @38
    @154
    eqid
    #
    @131
    @32
    @30
    @169
    @33
    syl
    @131
    @63
    @35
    wcel
    cX
    cc
    @63
    wf
    @60
    cZ
    @35
    @62
    cF
    wph
    cZ
    @35
    cF
    wf
    @1
    @59
    ulmdv.f
    ad2antrr
    ffvelrnda
    @63
    cc
    cX
    elmapi
    syl
    #
    wph
    cX
    cS
    wss
    #
    @1
    @59
    @116
    wph
    @18
    @172
    vk
    cZ
    wral
    @172
    @22
    wph
    @172
    vk
    cZ
    @36
    ralrimiva
    @172
    @172
    vk
    cM
    cZ
    @39
    @172
    biidd
    rspcv
    sylc
    #
    ad3antrrr
    eldv
    mpbid
    simprd
    @131
    vs
    vw
    vv
    @9
    @0
    @80
    @154
    @131
    vy
    @9
    @153
    cc
    @154
    @131
    @10
    @0
    cX
    @63
    @171
    @2
    cX
    cc
    wss
    @59
    @116
    @2
    cX
    cS
    cc
    wph
    @172
    @1
    @173
    adantr
    #
    wph
    @30
    @1
    @34
    adantr
    #
    sstrd
    #
    ad2antrr
    #
    @168
    dvlem
    @170
    fmptd
    @131
    cX
    cc
    @8
    @177
    ssdifssd
    @131
    cX
    cc
    @0
    @177
    @168
    sseldd
    ellimc3
    mpbid
    simprd
    @161
    @150
    vs
    @73
    crp
    @123
    @160
    @149
    vw
    crp
    @123
    @159
    @148
    vv
    @9
    @123
    @41
    @9
    wcel
    #
    wa
    @158
    @147
    @140
    @178
    @123
    @157
    @146
    @84
    @73
    clt
    @178
    @156
    @145
    cabs
    @178
    @155
    @144
    @80
    cmin
    vy
    @41
    @153
    @144
    @9
    @154
    vy
    vv
    weq
    #
    @152
    @143
    @14
    @43
    cdiv
    @179
    @151
    @141
    @142
    cmin
    @10
    @41
    @63
    fveq2
    oveq1d
    @10
    @41
    @0
    cmin
    oveq1
    #
    oveq12d
    @170
    @143
    @43
    cdiv
    ovex
    fvmpt
    oveq1d
    fveq2d
    @123
    id
    breqan12rd
    imbi2d
    ralbidva
    rexbidv
    rspcv
    sylc
    adantrr
    @137
    @138
    crp
    wcel
    #
    @149
    wa
    #
    wa
    #
    @45
    @138
    clt
    wbr
    #
    @0
    @45
    cabs
    cmin
    ccom
    #
    cS
    cS
    cxp
    cres
    #
    cbl
    cfv
    co
    cX
    wss
    #
    wa
    #
    @54
    vu
    crp
    @137
    @45
    crp
    wcel
    #
    @188
    wa
    #
    @182
    @54
    @137
    @190
    wa
    #
    @181
    @149
    @54
    @191
    @181
    wa
    #
    @148
    @53
    vv
    @9
    @192
    @178
    wa
    @148
    @47
    @41
    cG
    cfv
    #
    @12
    cmin
    co
    #
    @43
    cdiv
    co
    #
    @3
    cmin
    co
    #
    cabs
    cfv
    #
    @51
    clt
    wbr
    #
    wi
    #
    @53
    @192
    @178
    @148
    @199
    wi
    @192
    @178
    @148
    @47
    @198
    @192
    @137
    @190
    @181
    wa
    #
    wa
    @178
    @148
    @47
    w3a
    #
    @198
    @137
    @190
    @181
    anass
    @137
    @200
    @201
    @198
    @60
    @136
    @200
    @201
    wa
    #
    @198
    @136
    @202
    wa
    @60
    @116
    @134
    @202
    w3a
    #
    @198
    @116
    @134
    @202
    df-3an
    @60
    wph
    @1
    @59
    wa
    #
    wa
    @203
    @198
    wph
    @1
    @59
    anass
    wph
    @204
    @203
    @198
    wph
    @204
    @203
    wa
    #
    vx
    vs
    @0
    @51
    cS
    @45
    vk
    vm
    cF
    cG
    cH
    cM
    @62
    @138
    cX
    @41
    cZ
    ulmdv.z
    ulmdv.s
    ulmdv.m
    ulmdv.f
    ulmdv.g
    wph
    vk
    cZ
    @0
    @26
    cfv
    #
    cmpt
    #
    @12
    cli
    wbr
    #
    vz
    cX
    wral
    @84
    cX
    wcel
    vk
    cZ
    @84
    @26
    cfv
    #
    cmpt
    #
    @84
    cG
    cfv
    #
    cli
    wbr
    #
    wph
    @208
    vz
    cX
    ulmdv.l
    ralrimiva
    @208
    @212
    vz
    @84
    cX
    vz
    vs
    weq
    #
    @207
    @210
    @12
    @211
    cli
    @213
    vk
    cZ
    @206
    @209
    @0
    @84
    @26
    fveq2
    mpteq2dv
    @0
    @84
    cG
    fveq2
    breq12d
    rspccva
    sylan
    ulmdv.u
    wph
    @1
    @59
    @203
    simprll
    wph
    @1
    @59
    @203
    simprlr
    wph
    @205
    wa
    #
    @202
    @189
    @116
    @134
    @202
    @204
    wph
    simprr3
    #
    @189
    @188
    @181
    @201
    simplll
    syl
    @214
    @202
    @181
    @215
    @190
    @181
    @201
    simplr
    syl
    @214
    @184
    @187
    @214
    @202
    @188
    @215
    @189
    @188
    @181
    @201
    simpllr
    syl
    #
    simpld
    @214
    @184
    @187
    @216
    simprd
    @214
    @42
    @46
    @214
    @202
    @47
    @215
    @200
    @178
    @148
    @47
    simpr3
    syl
    #
    simprd
    @116
    @134
    @202
    @204
    wph
    simprr1
    @214
    @76
    @81
    @116
    @134
    @202
    @204
    wph
    simprr2
    #
    simpld
    @214
    @76
    @81
    @218
    simprd
    @214
    @41
    cX
    @8
    @214
    @202
    @178
    @215
    @200
    @178
    @148
    @47
    simpr1
    syl
    eldifad
    @214
    @42
    @46
    @217
    simpld
    #
    @214
    @42
    @139
    @147
    @219
    @214
    @202
    @148
    @215
    @200
    @178
    @148
    @47
    simpr2
    syl
    mpand
    ulmdvlem1
    anassrs
    sylanb
    sylan2br
    anassrs
    anassrs
    sylanb
    3exp2
    imp
    @178
    @53
    @199
    wb
    @192
    @178
    @52
    @198
    @47
    @178
    @50
    @197
    @51
    clt
    @178
    @49
    @196
    cabs
    @178
    @48
    @195
    @3
    cmin
    vy
    @41
    @15
    @195
    @9
    @16
    @179
    @13
    @194
    @14
    @43
    cdiv
    @179
    @11
    @193
    @12
    cmin
    @10
    @41
    cG
    fveq2
    oveq1d
    @180
    oveq12d
    @16
    eqid
    #
    @194
    @43
    cdiv
    ovex
    fvmpt
    oveq1d
    fveq2d
    breq1d
    imbi2d
    adantl
    sylibrd
    ralimdva
    impr
    an32s
    @183
    @186
    cS
    cxmt
    cfv
    wcel
    #
    cX
    @186
    cmopn
    cfv
    #
    wcel
    #
    @1
    @181
    @188
    vu
    crp
    wrex
    @2
    @221
    @59
    @136
    @182
    @2
    @185
    cc
    cxmt
    cfv
    wcel
    #
    @30
    @221
    cnxmet
    @175
    @185
    cS
    cc
    xmetres2
    sylancr
    ad3antrrr
    @2
    @223
    @59
    @136
    @182
    wph
    @223
    @1
    wph
    cX
    @5
    @222
    wph
    cX
    @5
    wcel
    #
    @6
    cX
    wceq
    #
    wph
    @6
    cX
    wph
    @5
    ctop
    wcel
    #
    cX
    @5
    cuni
    #
    wss
    #
    @6
    cX
    wss
    wph
    @4
    ctop
    wcel
    @32
    @227
    @4
    @38
    cnfldtop
    ulmdv.s
    cS
    @4
    @31
    resttop
    sylancr
    #
    wph
    cX
    cS
    @228
    @173
    wph
    @5
    cS
    ctopon
    cfv
    wcel
    #
    cS
    @228
    wceq
    wph
    @4
    cc
    ctopon
    cfv
    wcel
    @30
    @231
    @4
    @38
    cnfldtopon
    @34
    cS
    @4
    cc
    resttopon
    sylancr
    cS
    @5
    toponuni
    syl
    sseqtrd
    #
    cX
    @5
    @228
    @228
    eqid
    #
    ntrss2
    syl2anc
    @40
    eqssd
    wph
    @227
    @229
    @225
    @226
    wb
    @230
    @232
    cX
    @5
    @228
    @233
    isopn3
    syl2anc
    mpbird
    wph
    @224
    @30
    @5
    @222
    wceq
    cnxmet
    @34
    @185
    @186
    @4
    @222
    cc
    cS
    @186
    eqid
    @4
    @38
    cnfldtopn
    @222
    eqid
    #
    metrest
    sylancr
    eleqtrd
    adantr
    ad3antrrr
    @60
    @1
    @136
    @182
    @130
    ad2antrr
    @137
    @181
    @149
    simprl
    vu
    cX
    @186
    @0
    @138
    @222
    cS
    @234
    mopni3
    syl31anc
    reximddv
    rexlimddv
    rexlimdvaa
    syl5
    mp2and
    ralrimiva
    @2
    vr
    vu
    vv
    @9
    @0
    @3
    @16
    @2
    vy
    @9
    @15
    cc
    @16
    @2
    @10
    @0
    cX
    cG
    wph
    cX
    cc
    cG
    wf
    @1
    ulmdv.g
    adantr
    #
    @176
    wph
    @1
    simpr
    #
    dvlem
    @220
    fmptd
    @2
    cX
    cc
    @8
    @176
    ssdifssd
    @2
    cX
    cc
    @0
    @176
    @236
    sseldd
    ellimc3
    mpbir2and
    @2
    vy
    cX
    @0
    @3
    cS
    @5
    cG
    @16
    @4
    @37
    @38
    @220
    @175
    @235
    @174
    eldv
    mpbir2and
end
