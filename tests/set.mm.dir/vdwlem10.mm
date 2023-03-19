include "cn.mm"
include "wcel.mm"
include "cop.mm"
include "cv.mm"
include "cvdwp.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cvdwm.mm"
include "wo.mm"
include "cfz.mm"
include "cmap.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wceq.mm"
include "opeq1.mm"
include "breq1d.mm"
include "orbi1d.mm"
include "rexralbidv.mm"
include "imbi2d.mm"
include "weq.mm"
include "cfn.mm"
include "oveq1.mm"
include "raleqdv.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "wa.mm"
include "breq2.mm"
include "cbvralv.mm"
include "c2.mm"
include "cmul.mm"
include "2nn.mm"
include "simpr.mm"
include "nnmulcl.mm"
include "sylancr.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "adantr.mm"
include "ovex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "biimpa.mm"
include "cfv.mm"
include "cmpt.mm"
include "simplr.mm"
include "cle.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnred.mm"
include "simpllr.mm"
include "elfzle2.mm"
include "leadd1dd.mm"
include "nncnd.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "cuz.mm"
include "cz.mm"
include "nnaddcld.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "ad2antrr.mm"
include "nnzd.mm"
include "elfz5.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ffvelrnd.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "fmptd.mm"
include "biimpar.mm"
include "syldan.mm"
include "syl.mm"
include "cvdwa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wex.mm"
include "cn0.mm"
include "2nn0.mm"
include "eluznn0.mm"
include "vdwmc.mm"
include "vex.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprr.mm"
include "vdwlem8.mm"
include "orcd.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "exlimdv.mm"
include "sylbid.mm"
include "syld.mm"
include "ralrimdva.mm"
include "rspcev.mm"
include "syl6an.mm"
include "syl5bi.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "orbi12d.mm"
include "syl5bb.mm"
include "fzfi.mm"
include "mapfi.mm"
include "simprrl.mm"
include "mpan.mm"
include "sylan2.mm"
include "w3a.mm"
include "cmin.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2ll.mm"
include "simp2lr.mm"
include "simp2rl.mm"
include "simp2rr.mm"
include "simp3.mm"
include "mpbid.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "vdwlem9.mm"
include "3expia.mm"
include "ralrimiv.mm"
include "syl6bb.mm"
include "anassrs.mm"
include "rexlimddv.mm"
include "rexlimdvaa.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "mpcom.mm"

theorem vdwlem10
  let wph: wff ph
  let cR: class R
  let vf: setvar f
  let vn: setvar n
  let cK: class K
  let cM: class M
  let vs: setvar s
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  let cW: class W
  let cF: class F
  let vr: setvar r
  let cH: class H
  assume vdw.r: |- ( ph -> R e. Fin )
  assume vdwlem9.k: |- ( ph -> K e. ( ZZ>= ` 2 ) )
  assume vdwlem9.s: |- ( ph -> A. s e. Fin E. n e. NN A. f e. ( s ^m ( 1 ... n ) ) K MonoAP f )
  assume vdwlem10.m: |- ( ph -> M e. NN )

  disjoint f ph
  disjoint n ph
  disjoint f n
  disjoint f s
  disjoint K f
  disjoint n s
  disjoint K n
  disjoint K s
  disjoint M f
  disjoint M n
  disjoint R f
  disjoint R n
  disjoint R s
  disjoint a c
  disjoint a d
  disjoint a g
  disjoint a h
  disjoint a i
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint c d
  disjoint c g
  disjoint c h
  disjoint c i
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint c ph
  disjoint d g
  disjoint d h
  disjoint d i
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint d ph
  disjoint g h
  disjoint g i
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint g ph
  disjoint h i
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint h ph
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint i ph
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint k ph
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint m ph
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint ph u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint V f
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint W f
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint a f
  disjoint F a
  disjoint c f
  disjoint F c
  disjoint d f
  disjoint F d
  disjoint f g
  disjoint f w
  disjoint F f
  disjoint F g
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint a r
  disjoint a s
  disjoint K a
  disjoint c r
  disjoint c s
  disjoint K c
  disjoint d r
  disjoint d s
  disjoint K d
  disjoint f h
  disjoint f i
  disjoint f k
  disjoint f m
  disjoint f r
  disjoint f u
  disjoint f v
  disjoint g r
  disjoint g s
  disjoint K g
  disjoint h r
  disjoint h s
  disjoint K h
  disjoint i r
  disjoint i s
  disjoint K i
  disjoint k r
  disjoint k s
  disjoint K k
  disjoint m r
  disjoint m s
  disjoint K m
  disjoint n r
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint K r
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint M a
  disjoint M d
  disjoint M g
  disjoint M x
  disjoint M y
  disjoint R a
  disjoint R c
  disjoint R d
  disjoint R g
  disjoint R h
  disjoint R i
  disjoint R k
  disjoint R m
  disjoint R r
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint H a
  disjoint H d
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint H z
  assert |- ( ph -> E. n e. NN A. f e. ( R ^m ( 1 ... n ) ) ( <. M , K >. PolyAP f \/ ( K + 1 ) MonoAP f ) )

  proof
    cM
    cn
    wcel
    wph
    cM
    cK
    cop
    #
    vf
    cv
    #
    cvdwp
    wbr
    #
    cK
    c1
    caddc
    co
    #
    @1
    cvdwm
    wbr
    #
    wo
    #
    vf
    cR
    c1
    vn
    cv
    #
    cfz
    co
    #
    cmap
    co
    #
    wral
    vn
    cn
    wrex
    #
    vdwlem10.m
    wph
    vx
    cv
    #
    cK
    cop
    #
    @1
    cvdwp
    wbr
    #
    @4
    wo
    #
    vf
    @8
    wral
    vn
    cn
    wrex
    #
    wi
    wph
    c1
    cK
    cop
    #
    @1
    cvdwp
    wbr
    #
    @4
    wo
    #
    vf
    @8
    wral
    #
    vn
    cn
    wrex
    #
    wi
    wph
    vm
    cv
    #
    cK
    cop
    #
    @1
    cvdwp
    wbr
    #
    @4
    wo
    #
    vf
    @8
    wral
    #
    vn
    cn
    wrex
    #
    wi
    wph
    @20
    c1
    caddc
    co
    #
    cK
    cop
    #
    @1
    cvdwp
    wbr
    #
    @4
    wo
    #
    vf
    @8
    wral
    #
    vn
    cn
    wrex
    #
    wi
    wph
    @9
    wi
    vx
    vm
    cM
    @10
    c1
    wceq
    #
    @14
    @19
    wph
    @32
    @13
    @17
    vn
    vf
    cn
    @8
    @32
    @12
    @16
    @4
    @32
    @11
    @15
    @1
    cvdwp
    @10
    c1
    cK
    opeq1
    breq1d
    orbi1d
    rexralbidv
    imbi2d
    vx
    vm
    weq
    #
    @14
    @25
    wph
    @33
    @13
    @23
    vn
    vf
    cn
    @8
    @33
    @12
    @22
    @4
    @33
    @11
    @21
    @1
    cvdwp
    @10
    @20
    cK
    opeq1
    breq1d
    orbi1d
    rexralbidv
    imbi2d
    @10
    @26
    wceq
    #
    @14
    @31
    wph
    @34
    @13
    @29
    vn
    vf
    cn
    @8
    @34
    @12
    @28
    @4
    @34
    @11
    @27
    @1
    cvdwp
    @10
    @26
    cK
    opeq1
    breq1d
    orbi1d
    rexralbidv
    imbi2d
    @10
    cM
    wceq
    #
    @14
    @9
    wph
    @35
    @13
    @5
    vn
    vf
    cn
    @8
    @35
    @12
    @2
    @4
    @35
    @11
    @0
    @1
    cvdwp
    @10
    cM
    cK
    opeq1
    breq1d
    orbi1d
    rexralbidv
    imbi2d
    wph
    cK
    @1
    cvdwm
    wbr
    #
    vf
    cR
    c1
    vw
    cv
    #
    cfz
    co
    #
    cmap
    co
    #
    wral
    #
    vw
    cn
    wrex
    #
    @19
    wph
    @36
    vf
    @8
    wral
    #
    vn
    cn
    wrex
    #
    @41
    wph
    cR
    cfn
    wcel
    #
    @36
    vf
    vs
    cv
    #
    @7
    cmap
    co
    #
    wral
    #
    vn
    cn
    wrex
    #
    vs
    cfn
    wral
    #
    @43
    vdw.r
    vdwlem9.s
    @48
    @43
    vs
    cR
    cfn
    @45
    cR
    wceq
    #
    @47
    @42
    vn
    cn
    @50
    @36
    vf
    @46
    @8
    @45
    cR
    @7
    cmap
    oveq1
    raleqdv
    rexbidv
    rspcv
    sylc
    @42
    @40
    vn
    vw
    cn
    vn
    vw
    weq
    #
    @36
    vf
    @8
    @39
    @51
    @7
    @38
    cR
    cmap
    @6
    @37
    c1
    cfz
    oveq2
    oveq2d
    #
    raleqdv
    cbvrexv
    sylib
    wph
    @40
    @19
    vw
    cn
    @40
    cK
    vg
    cv
    #
    cvdwm
    wbr
    #
    vg
    @39
    wral
    #
    wph
    @37
    cn
    wcel
    #
    wa
    #
    @19
    @36
    @54
    vf
    vg
    @39
    @1
    @53
    cK
    cvdwm
    breq2
    cbvralv
    @57
    c2
    @37
    cmul
    co
    #
    cn
    wcel
    #
    @55
    @17
    vf
    cR
    c1
    @58
    cfz
    co
    #
    cmap
    co
    #
    wral
    #
    @19
    @57
    c2
    cn
    wcel
    #
    @56
    @59
    2nn
    wph
    @56
    simpr
    c2
    @37
    nnmulcl
    sylancr
    #
    @57
    @55
    @17
    vf
    @61
    @57
    @1
    @61
    wcel
    #
    @60
    cR
    @1
    wf
    #
    @55
    @17
    wi
    @57
    @65
    @66
    @57
    @44
    @60
    cvv
    wcel
    @65
    @66
    wb
    wph
    @44
    @56
    vdw.r
    adantr
    #
    c1
    @58
    cfz
    ovex
    cR
    @60
    @1
    cfn
    cvv
    elmapg
    sylancl
    biimpa
    @57
    @66
    wa
    #
    @55
    cK
    vx
    @38
    @10
    @37
    caddc
    co
    #
    @1
    cfv
    #
    cmpt
    #
    cvdwm
    wbr
    #
    @17
    @68
    @71
    @39
    wcel
    #
    @55
    @72
    wi
    @57
    @66
    @38
    cR
    @71
    wf
    #
    @73
    @68
    vy
    @38
    vy
    cv
    #
    @37
    caddc
    co
    #
    @1
    cfv
    #
    cR
    @71
    @68
    @75
    @38
    wcel
    #
    wa
    #
    @60
    cR
    @76
    @1
    @57
    @66
    @78
    simplr
    @79
    @76
    @60
    wcel
    #
    @76
    @58
    cle
    wbr
    #
    @79
    @76
    @37
    @37
    caddc
    co
    @58
    cle
    @79
    @75
    @37
    @37
    @79
    @75
    @78
    @75
    cn
    wcel
    @68
    @75
    @37
    elfznn
    adantl
    #
    nnred
    @79
    @37
    wph
    @56
    @66
    @78
    simpllr
    #
    nnred
    #
    @84
    @78
    @75
    @37
    cle
    wbr
    @68
    @75
    c1
    @37
    elfzle2
    adantl
    leadd1dd
    @79
    @37
    @79
    @37
    @83
    nncnd
    2timesd
    breqtrrd
    @79
    @76
    c1
    cuz
    cfv
    #
    wcel
    @58
    cz
    wcel
    @80
    @81
    wb
    @79
    @76
    cn
    @85
    @79
    @75
    @37
    @82
    @83
    nnaddcld
    nnuz
    syl6eleq
    @79
    @58
    @57
    @59
    @66
    @78
    @64
    ad2antrr
    nnzd
    @76
    c1
    @58
    elfz5
    syl2anc
    mpbird
    ffvelrnd
    vx
    vy
    @38
    @70
    @77
    vx
    vy
    weq
    @69
    @76
    @1
    @10
    @75
    @37
    caddc
    oveq1
    fveq2d
    cbvmptv
    #
    fmptd
    #
    @57
    @73
    @74
    @57
    @44
    @38
    cvv
    wcel
    @73
    @74
    wb
    @67
    c1
    @37
    cfz
    ovex
    #
    cR
    @38
    @71
    cfn
    cvv
    elmapg
    sylancl
    biimpar
    syldan
    @54
    @72
    vg
    @71
    @39
    @53
    @71
    cK
    cvdwm
    breq2
    rspcv
    syl
    @68
    @72
    va
    cv
    #
    vd
    cv
    #
    cK
    cvdwa
    cfv
    co
    @71
    ccnv
    vc
    cv
    #
    csn
    cima
    wss
    #
    vd
    cn
    wrex
    va
    cn
    wrex
    #
    vc
    wex
    @17
    @68
    cR
    @71
    cK
    @38
    va
    vc
    vd
    @88
    @68
    c2
    cn0
    wcel
    cK
    c2
    cuz
    cfv
    wcel
    #
    cK
    cn0
    wcel
    2nn0
    wph
    @94
    @56
    @66
    vdwlem9.k
    ad2antrr
    #
    cK
    c2
    eluznn0
    sylancr
    @87
    vdwmc
    @68
    @93
    @17
    vc
    @68
    @92
    @17
    va
    vd
    cn
    cn
    @68
    @89
    cn
    wcel
    #
    @90
    cn
    wcel
    #
    wa
    #
    @92
    @17
    @68
    @98
    @92
    wa
    #
    wa
    #
    @16
    @4
    @100
    vy
    @89
    @91
    @90
    cR
    @1
    @71
    cK
    @37
    @57
    @44
    @66
    @99
    @67
    ad2antrr
    @68
    @94
    @99
    @95
    adantr
    wph
    @56
    @66
    @99
    simpllr
    @57
    @66
    @99
    simplr
    vc
    vex
    @68
    @96
    @97
    @92
    simprll
    @68
    @96
    @97
    @92
    simprlr
    @68
    @98
    @92
    simprr
    @86
    vdwlem8
    orcd
    expr
    rexlimdvva
    exlimdv
    sylbid
    syld
    syldan
    ralrimdva
    @18
    @62
    vn
    @58
    cn
    @6
    @58
    wceq
    #
    @17
    vf
    @8
    @61
    @101
    @7
    @60
    cR
    cmap
    @6
    @58
    c1
    cfz
    oveq2
    oveq2d
    raleqdv
    rspcev
    syl6an
    syl5bi
    rexlimdva
    mpd
    @20
    cn
    wcel
    #
    wph
    @25
    @31
    wph
    @102
    @25
    @31
    wi
    @25
    @21
    @53
    cvdwp
    wbr
    #
    @3
    @53
    cvdwm
    wbr
    #
    wo
    #
    vg
    @39
    wral
    #
    vw
    cn
    wrex
    wph
    @102
    wa
    #
    @31
    @24
    @106
    vn
    vw
    cn
    @24
    @105
    vg
    @8
    wral
    @51
    @106
    @23
    @105
    vf
    vg
    @8
    vf
    vg
    weq
    @22
    @103
    @4
    @104
    @1
    @53
    @21
    cvdwp
    breq2
    @1
    @53
    @3
    cvdwm
    breq2
    orbi12d
    cbvralv
    @51
    @105
    vg
    @8
    @39
    @52
    raleqdv
    syl5bb
    cbvrexv
    @107
    @106
    @31
    vw
    cn
    @107
    @56
    @106
    wa
    #
    wa
    #
    @36
    vf
    @39
    c1
    vv
    cv
    #
    cfz
    co
    #
    cmap
    co
    #
    wral
    #
    @31
    vv
    cn
    @109
    @39
    cfn
    wcel
    #
    @49
    @113
    vv
    cn
    wrex
    #
    @109
    @44
    @38
    cfn
    wcel
    @114
    wph
    @44
    @102
    @108
    vdw.r
    ad2antrr
    c1
    @37
    fzfi
    cR
    @38
    mapfi
    sylancl
    wph
    @49
    @102
    @108
    vdwlem9.s
    ad2antrr
    @48
    @115
    vs
    @39
    cfn
    @48
    @36
    vf
    @45
    @111
    cmap
    co
    #
    wral
    #
    vv
    cn
    wrex
    @45
    @39
    wceq
    #
    @115
    @47
    @117
    vn
    vv
    cn
    vn
    vv
    weq
    #
    @36
    vf
    @46
    @116
    @119
    @7
    @111
    @45
    cmap
    @6
    @110
    c1
    cfz
    oveq2
    oveq2d
    raleqdv
    cbvrexv
    @118
    @117
    @113
    vv
    cn
    @118
    @36
    vf
    @116
    @112
    @45
    @39
    @111
    cmap
    oveq1
    raleqdv
    rexbidv
    syl5bb
    rspcv
    sylc
    @107
    @108
    @110
    cn
    wcel
    #
    @113
    wa
    #
    @31
    @107
    @108
    @121
    wa
    #
    wa
    #
    @37
    c2
    @110
    cmul
    co
    #
    cmul
    co
    #
    cn
    wcel
    #
    @27
    vh
    cv
    #
    cvdwp
    wbr
    #
    @3
    @127
    cvdwm
    wbr
    #
    wo
    #
    vh
    cR
    c1
    @125
    cfz
    co
    #
    cmap
    co
    #
    wral
    #
    @31
    @123
    @56
    @120
    @126
    @107
    @56
    @106
    @121
    simprll
    @107
    @108
    @120
    @113
    simprrl
    @120
    @56
    @124
    cn
    wcel
    #
    @126
    @63
    @120
    @134
    2nn
    c2
    @110
    nnmulcl
    mpan
    @37
    @124
    nnmulcl
    sylan2
    syl2anc
    @123
    @130
    vh
    @132
    @107
    @122
    @127
    @132
    wcel
    #
    @130
    @107
    @122
    @135
    w3a
    #
    vz
    vu
    cR
    vf
    vk
    vn
    vx
    @111
    vy
    @38
    @75
    @37
    @10
    c1
    cmin
    co
    #
    @110
    caddc
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @127
    cfv
    #
    cmpt
    #
    cmpt
    @127
    cK
    @20
    @110
    @37
    vs
    @136
    wph
    @44
    wph
    @102
    @122
    @135
    simp1l
    #
    vdw.r
    syl
    #
    @136
    wph
    @94
    @143
    vdwlem9.k
    syl
    @136
    wph
    @49
    @143
    vdwlem9.s
    syl
    wph
    @102
    @122
    @135
    simp1r
    @56
    @106
    @121
    @107
    @135
    simp2ll
    @136
    @106
    @21
    vk
    cv
    #
    cvdwp
    wbr
    #
    @3
    @145
    cvdwm
    wbr
    #
    wo
    #
    vk
    @39
    wral
    @56
    @106
    @121
    @107
    @135
    simp2lr
    @105
    @148
    vg
    vk
    @39
    vg
    vk
    weq
    @103
    @146
    @104
    @147
    @53
    @145
    @21
    cvdwp
    breq2
    @53
    @145
    @3
    cvdwm
    breq2
    orbi12d
    cbvralv
    sylib
    @120
    @113
    @108
    @107
    @135
    simp2rl
    @120
    @113
    @108
    @107
    @135
    simp2rr
    @136
    @135
    @131
    cR
    @127
    wf
    #
    @107
    @122
    @135
    simp3
    @136
    @44
    @131
    cvv
    wcel
    @135
    @149
    wb
    @144
    c1
    @125
    cfz
    ovex
    cR
    @131
    @127
    cfn
    cvv
    elmapg
    sylancl
    mpbid
    vx
    vz
    @111
    @142
    vu
    @38
    vu
    cv
    #
    @37
    vz
    cv
    #
    c1
    cmin
    co
    #
    @110
    caddc
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @127
    cfv
    #
    cmpt
    #
    vx
    vz
    weq
    #
    @142
    vu
    @38
    @150
    @139
    caddc
    co
    #
    @127
    cfv
    #
    cmpt
    @157
    vy
    vu
    @38
    @141
    @160
    vy
    vu
    weq
    @140
    @159
    @127
    @75
    @150
    @139
    caddc
    oveq1
    fveq2d
    cbvmptv
    @158
    vu
    @38
    @160
    @156
    @158
    @159
    @155
    @127
    @158
    @139
    @154
    @150
    caddc
    @158
    @138
    @153
    @37
    cmul
    @158
    @137
    @152
    @110
    caddc
    @10
    @151
    c1
    cmin
    oveq1
    oveq1d
    oveq2d
    oveq2d
    fveq2d
    mpteq2dv
    syl5eq
    cbvmptv
    vdwlem9
    3expia
    ralrimiv
    @30
    @133
    vn
    @125
    cn
    @6
    @125
    wceq
    #
    @30
    @29
    vf
    @132
    wral
    @133
    @161
    @29
    vf
    @8
    @132
    @161
    @7
    @131
    cR
    cmap
    @6
    @125
    c1
    cfz
    oveq2
    oveq2d
    raleqdv
    @29
    @130
    vf
    vh
    @132
    vf
    vh
    weq
    @28
    @128
    @4
    @129
    @1
    @127
    @27
    cvdwp
    breq2
    @1
    @127
    @3
    cvdwm
    breq2
    orbi12d
    cbvralv
    syl6bb
    rspcev
    syl2anc
    anassrs
    rexlimddv
    rexlimdvaa
    syl5bi
    expcom
    a2d
    nnind
    mpcom
end
