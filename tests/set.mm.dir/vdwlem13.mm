include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cvdwm.mm"
include "wbr.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wral.mm"
include "wrex.mm"
include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wo.mm"
include "elnn1uz2.mm"
include "cvdwa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wf.mm"
include "cfn.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "biimpa.mm"
include "wa.mm"
include "1nn.mm"
include "vdwap1.mm"
include "mp2an.mm"
include "cz.mm"
include "1z.mm"
include "elfz3.mm"
include "mp1i.mm"
include "eqidd.mm"
include "wfn.mm"
include "ffn.mm"
include "adantl.mm"
include "fniniseg.mm"
include "syl.mm"
include "mpbir2and.mm"
include "snssd.mm"
include "syl5eqss.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "oveqd.mm"
include "sseq1d.mm"
include "ralbidv.mm"
include "syl5ibrcom.mm"
include "wex.mm"
include "oveq1.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "mp3an12.mm"
include "fvex.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "sseq2d.mm"
include "2rexbidv.mm"
include "spcev.mm"
include "cn0.mm"
include "adantr.mm"
include "vdwmc.mm"
include "syl5ibr.mm"
include "ralimdva.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "mpan.mm"
include "syl6.mm"
include "syld.mm"
include "caddc.mm"
include "breq1.mm"
include "rexralbidv.mm"
include "weq.mm"
include "chash.mm"
include "hashcl.mm"
include "nn0p1nn.mm"
include "wi.mm"
include "wn.mm"
include "simpll.mm"
include "simplr.mm"
include "vex.mm"
include "elmap.mm"
include "sylib.mm"
include "simpr.mm"
include "vdwlem12.mm"
include "iman.mm"
include "mpbir.mm"
include "syl2anc.mm"
include "rgen.mm"
include "a1i.mm"
include "rexbidv.mm"
include "breq2.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "cbvrexv.mm"
include "ralbii.mm"
include "sylibr.mm"
include "vdwlem11.mm"
include "ex.mm"
include "ralrimdva.mm"
include "syl5bi.mm"
include "uzind4.mm"
include "rspcv.mm"
include "syl2im.mm"
include "jaod.mm"
include "c0.mm"
include "vdwap0.mm"
include "syl6eq.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "ralrimivw.mm"
include "syl5.mm"
include "elnn0.mm"
include "mpjaod.mm"

theorem vdwlem13
  let wph: wff ph
  let cR: class R
  let vf: setvar f
  let vn: setvar n
  let cK: class K
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
  let vs: setvar s
  let cM: class M
  let cH: class H
  assume vdw.r: |- ( ph -> R e. Fin )
  assume vdw.k: |- ( ph -> K e. NN0 )

  disjoint n ph
  disjoint f n
  disjoint K f
  disjoint K n
  disjoint R f
  disjoint R n
  disjoint f ph
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
  disjoint f s
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
  disjoint n s
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
  disjoint K s
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint M a
  disjoint M d
  disjoint M f
  disjoint M g
  disjoint M n
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
  disjoint R s
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
  assert |- ( ph -> E. n e. NN A. f e. ( R ^m ( 1 ... n ) ) K MonoAP f )

  proof
    wph
    cK
    cn
    wcel
    #
    cK
    vf
    cv
    #
    cvdwm
    wbr
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
    #
    vn
    cn
    wrex
    #
    cK
    cc0
    wceq
    #
    @0
    cK
    c1
    wceq
    #
    cK
    c2
    cuz
    cfv
    #
    wcel
    #
    wo
    wph
    @7
    cK
    elnn1uz2
    wph
    @9
    @7
    @11
    wph
    @9
    c1
    c1
    cK
    cvdwa
    cfv
    #
    co
    #
    @1
    ccnv
    #
    c1
    @1
    cfv
    #
    csn
    #
    cima
    #
    wss
    #
    vf
    cR
    c1
    c1
    cfz
    co
    #
    cmap
    co
    #
    wral
    #
    @7
    wph
    @21
    @9
    c1
    c1
    c1
    cvdwa
    cfv
    #
    co
    #
    @17
    wss
    #
    vf
    @20
    wral
    wph
    @24
    vf
    @20
    wph
    @1
    @20
    wcel
    #
    @19
    cR
    @1
    wf
    #
    @24
    wph
    @25
    @26
    wph
    cR
    cfn
    wcel
    #
    @19
    cvv
    wcel
    @25
    @26
    wb
    vdw.r
    c1
    c1
    cfz
    ovex
    #
    cR
    @19
    @1
    cfn
    cvv
    elmapg
    sylancl
    biimpa
    #
    wph
    @26
    wa
    #
    @23
    c1
    csn
    #
    @17
    c1
    cn
    wcel
    #
    @32
    @23
    @31
    wceq
    1nn
    1nn
    c1
    c1
    vdwap1
    mp2an
    @30
    c1
    @17
    @30
    c1
    @17
    wcel
    #
    c1
    @19
    wcel
    #
    @15
    @15
    wceq
    #
    c1
    cz
    wcel
    @34
    @30
    1z
    c1
    elfz3
    mp1i
    @30
    @15
    eqidd
    @30
    @1
    @19
    wfn
    #
    @33
    @34
    @35
    wa
    wb
    @26
    @36
    wph
    @19
    cR
    @1
    ffn
    adantl
    @19
    @15
    c1
    @1
    fniniseg
    syl
    mpbir2and
    snssd
    syl5eqss
    syldan
    ralrimiva
    @9
    @18
    @24
    vf
    @20
    @9
    @13
    @23
    @17
    @9
    @12
    @22
    c1
    c1
    cK
    c1
    cvdwa
    fveq2
    oveqd
    sseq1d
    ralbidv
    syl5ibrcom
    wph
    @21
    @2
    vf
    @20
    wral
    #
    @7
    wph
    @18
    @2
    vf
    @20
    @18
    @2
    wph
    @25
    wa
    #
    va
    cv
    #
    vd
    cv
    #
    @12
    co
    #
    @14
    vc
    cv
    #
    csn
    #
    cima
    #
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
    #
    @18
    @41
    @17
    wss
    #
    vd
    cn
    wrex
    va
    cn
    wrex
    #
    @47
    @32
    @32
    @18
    @49
    1nn
    1nn
    @48
    @18
    c1
    @40
    @12
    co
    #
    @17
    wss
    va
    vd
    c1
    c1
    cn
    cn
    @39
    c1
    wceq
    @41
    @50
    @17
    @39
    c1
    @40
    @12
    oveq1
    sseq1d
    @40
    c1
    wceq
    @50
    @13
    @17
    @40
    c1
    c1
    @12
    oveq2
    sseq1d
    rspc2ev
    mp3an12
    @46
    @49
    vc
    @15
    c1
    @1
    fvex
    @42
    @15
    wceq
    #
    @45
    @48
    va
    vd
    cn
    cn
    @51
    @44
    @17
    @41
    @51
    @43
    @16
    @14
    @42
    @15
    sneq
    imaeq2d
    sseq2d
    2rexbidv
    spcev
    syl
    @38
    cR
    @1
    cK
    @19
    va
    vc
    vd
    @28
    wph
    cK
    cn0
    wcel
    #
    @25
    vdw.k
    adantr
    @29
    vdwmc
    syl5ibr
    ralimdva
    @32
    @37
    @7
    1nn
    @6
    @37
    vn
    c1
    cn
    @3
    c1
    wceq
    #
    @2
    vf
    @5
    @20
    @53
    @4
    @19
    cR
    cmap
    @3
    c1
    c1
    cfz
    oveq2
    oveq2d
    raleqdv
    rspcev
    mpan
    syl6
    #
    syld
    wph
    @27
    @11
    @2
    vf
    vr
    cv
    #
    @4
    cmap
    co
    #
    wral
    #
    vn
    cn
    wrex
    #
    vr
    cfn
    wral
    #
    @7
    vdw.r
    vx
    cv
    #
    @1
    cvdwm
    wbr
    #
    vf
    @56
    wral
    vn
    cn
    wrex
    #
    vr
    cfn
    wral
    c2
    @1
    cvdwm
    wbr
    #
    vf
    @56
    wral
    #
    vn
    cn
    wrex
    #
    vr
    cfn
    wral
    #
    vk
    cv
    #
    @1
    cvdwm
    wbr
    #
    vf
    @56
    wral
    #
    vn
    cn
    wrex
    #
    vr
    cfn
    wral
    #
    @67
    c1
    caddc
    co
    #
    @1
    cvdwm
    wbr
    #
    vf
    @56
    wral
    vn
    cn
    wrex
    #
    vr
    cfn
    wral
    #
    @59
    vx
    vk
    c2
    cK
    @60
    c2
    wceq
    #
    @62
    @65
    vr
    cfn
    @76
    @61
    @63
    vn
    vf
    cn
    @56
    @60
    c2
    @1
    cvdwm
    breq1
    rexralbidv
    ralbidv
    vx
    vk
    weq
    #
    @62
    @70
    vr
    cfn
    @77
    @61
    @68
    vn
    vf
    cn
    @56
    @60
    @67
    @1
    cvdwm
    breq1
    rexralbidv
    ralbidv
    @60
    @72
    wceq
    #
    @62
    @74
    vr
    cfn
    @78
    @61
    @73
    vn
    vf
    cn
    @56
    @60
    @72
    @1
    cvdwm
    breq1
    rexralbidv
    ralbidv
    @60
    cK
    wceq
    #
    @62
    @58
    vr
    cfn
    @79
    @61
    @2
    vn
    vf
    cn
    @56
    @60
    cK
    @1
    cvdwm
    breq1
    rexralbidv
    ralbidv
    @66
    c2
    cz
    wcel
    @65
    vr
    cfn
    @55
    cfn
    wcel
    #
    @55
    chash
    cfv
    #
    c1
    caddc
    co
    #
    cn
    wcel
    #
    @63
    vf
    @55
    c1
    @82
    cfz
    co
    #
    cmap
    co
    #
    wral
    #
    @65
    @80
    @81
    cn0
    wcel
    @83
    @55
    hashcl
    @81
    nn0p1nn
    syl
    @80
    @63
    vf
    @85
    @80
    @1
    @85
    wcel
    #
    wa
    #
    @63
    wi
    @88
    @63
    wn
    #
    wa
    #
    wn
    @90
    @55
    @1
    @80
    @87
    @89
    simpll
    @90
    @87
    @84
    @55
    @1
    wf
    @80
    @87
    @89
    simplr
    @55
    @84
    @1
    vr
    vex
    c1
    @82
    cfz
    ovex
    elmap
    sylib
    @88
    @89
    simpr
    vdwlem12
    @88
    @63
    iman
    mpbir
    ralrimiva
    @64
    @86
    vn
    @82
    cn
    @3
    @82
    wceq
    #
    @63
    vf
    @56
    @85
    @91
    @4
    @84
    @55
    cmap
    @3
    @82
    c1
    cfz
    oveq2
    oveq2d
    raleqdv
    rspcev
    syl2anc
    rgen
    a1i
    @71
    @67
    vg
    cv
    #
    cvdwm
    wbr
    #
    vg
    vs
    cv
    #
    c1
    vm
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
    vm
    cn
    wrex
    #
    vs
    cfn
    wral
    #
    @67
    @10
    wcel
    #
    @75
    @70
    @99
    vr
    vs
    cfn
    vr
    vs
    weq
    #
    @70
    @68
    vf
    @94
    @4
    cmap
    co
    #
    wral
    #
    vn
    cn
    wrex
    #
    @99
    @102
    @69
    @104
    vn
    cn
    @102
    @68
    vf
    @56
    @103
    @55
    @94
    @4
    cmap
    oveq1
    raleqdv
    rexbidv
    @104
    @98
    vn
    vm
    cn
    vn
    vm
    weq
    #
    @104
    @68
    vf
    @97
    wral
    @98
    @106
    @68
    vf
    @103
    @97
    @106
    @4
    @96
    @94
    cmap
    @3
    @95
    c1
    cfz
    oveq2
    oveq2d
    raleqdv
    @68
    @93
    vf
    vg
    @97
    @1
    @92
    @67
    cvdwm
    breq2
    cbvralv
    syl6bb
    cbvrexv
    #
    syl6bb
    cbvralv
    @101
    @100
    @74
    vr
    cfn
    @101
    @80
    wa
    #
    @100
    @74
    @108
    @100
    wa
    #
    @55
    vf
    vn
    @67
    vs
    @101
    @80
    @100
    simplr
    @101
    @80
    @100
    simpll
    @109
    @100
    @105
    vs
    cfn
    wral
    @108
    @100
    simpr
    @105
    @99
    vs
    cfn
    @107
    ralbii
    sylibr
    vdwlem11
    ex
    ralrimdva
    syl5bi
    uzind4
    @58
    @7
    vr
    cR
    cfn
    @55
    cR
    wceq
    #
    @57
    @6
    vn
    cn
    @110
    @2
    vf
    @56
    @5
    @55
    cR
    @4
    cmap
    oveq1
    raleqdv
    rexbidv
    rspcv
    syl2im
    jaod
    syl5bi
    @8
    @21
    wph
    @7
    @8
    @18
    vf
    @20
    @8
    @13
    c0
    @17
    @8
    @13
    c1
    c1
    cc0
    cvdwa
    cfv
    #
    co
    #
    c0
    @8
    @12
    @111
    c1
    c1
    cK
    cc0
    cvdwa
    fveq2
    oveqd
    @32
    @32
    @112
    c0
    wceq
    1nn
    1nn
    c1
    c1
    vdwap0
    mp2an
    syl6eq
    @17
    0ss
    syl6eqss
    ralrimivw
    @54
    syl5
    wph
    @52
    @0
    @8
    wo
    vdw.k
    cK
    elnn0
    sylib
    mpjaod
end
