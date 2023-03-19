include "cvdwm.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cop.mm"
include "cvdwp.mm"
include "wo.mm"
include "cfz.mm"
include "cmap.mm"
include "wcel.mm"
include "cv.mm"
include "wral.mm"
include "wf.mm"
include "vdwlem4.mm"
include "ovex.mm"
include "elmap.mm"
include "sylibr.mm"
include "breq2.mm"
include "rspcv.mm"
include "sylc.mm"
include "cvdwa.mm"
include "cfv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "cn.mm"
include "wrex.mm"
include "wex.mm"
include "c2.mm"
include "cuz.mm"
include "eluz2nn.mm"
include "syl.mm"
include "nnnn0d.mm"
include "vdwmc.mm"
include "wa.mm"
include "adantr.mm"
include "wceq.mm"
include "simprr.mm"
include "simprll.mm"
include "simprlr.mm"
include "vdwapid1.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mpbid.mm"
include "simprd.mm"
include "simpld.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "rsp.mm"
include "cfn.mm"
include "cmul.mm"
include "cvv.mm"
include "elmapg.mm"
include "sylancl.mm"
include "vdwlem7.mm"
include "wi.mm"
include "olc.mm"
include "a1i.mm"
include "jaod.mm"
include "cmin.mm"
include "cmpt.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "mpteq2dv.mm"
include "mptex.mm"
include "fvmpt.mm"
include "eqtr3d.mm"
include "breq2d.mm"
include "cn0.mm"
include "peano2nn0.mm"
include "nnm1nn0.mm"
include "nn0nnaddcl.mm"
include "syl2anc.mm"
include "nnmulcld.mm"
include "cz.mm"
include "cle.mm"
include "nnaddcld.mm"
include "nnzd.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "sylancr.mm"
include "nnred.mm"
include "elfzle2.mm"
include "leadd1dd.mm"
include "nncnd.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "nngt0d.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "1cnd.mm"
include "nn0cnd.mm"
include "addcld.mm"
include "adddid.mm"
include "addassd.mm"
include "cc.mm"
include "ax-1cn.mm"
include "pncan3.mm"
include "mulid1d.mm"
include "3eqtr3d.mm"
include "eleqtrd.mm"
include "cbvmptv.mm"
include "vdwlem2.mm"
include "sylbird.mm"
include "orim2d.mm"
include "syld.mm"
include "mpd.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "exlimdv.mm"
include "sylbid.mm"

theorem vdwlem9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cK: class K
  let cM: class M
  let cV: class V
  let cW: class W
  let vs: setvar s
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vh: setvar h
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let vr: setvar r
  assume vdw.r: |- ( ph -> R e. Fin )
  assume vdwlem9.k: |- ( ph -> K e. ( ZZ>= ` 2 ) )
  assume vdwlem9.s: |- ( ph -> A. s e. Fin E. n e. NN A. f e. ( s ^m ( 1 ... n ) ) K MonoAP f )
  assume vdwlem9.m: |- ( ph -> M e. NN )
  assume vdwlem9.w: |- ( ph -> W e. NN )
  assume vdwlem9.g: |- ( ph -> A. g e. ( R ^m ( 1 ... W ) ) ( <. M , K >. PolyAP g \/ ( K + 1 ) MonoAP g ) )
  assume vdwlem9.v: |- ( ph -> V e. NN )
  assume vdwlem9.a: |- ( ph -> A. f e. ( ( R ^m ( 1 ... W ) ) ^m ( 1 ... V ) ) K MonoAP f )
  assume vdwlem9.h: |- ( ph -> H : ( 1 ... ( W x. ( 2 x. V ) ) ) --> R )
  assume vdwlem9.f: |- F = ( x e. ( 1 ... V ) |-> ( y e. ( 1 ... W ) |-> ( H ` ( y + ( W x. ( ( x - 1 ) + V ) ) ) ) ) )

  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g ph
  disjoint n x
  disjoint n y
  disjoint n ph
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint f x
  disjoint f y
  disjoint V f
  disjoint V x
  disjoint V y
  disjoint W f
  disjoint W x
  disjoint W y
  disjoint f g
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint f n
  disjoint f s
  disjoint K f
  disjoint g s
  disjoint K g
  disjoint n s
  disjoint K n
  disjoint s x
  disjoint s y
  disjoint K s
  disjoint K x
  disjoint K y
  disjoint M f
  disjoint M g
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint R f
  disjoint R g
  disjoint R n
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint H g
  disjoint H x
  disjoint H y
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
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g z
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
  disjoint x z
  disjoint y z
  disjoint ph z
  disjoint f z
  disjoint V z
  disjoint W z
  disjoint a f
  disjoint F a
  disjoint c f
  disjoint F c
  disjoint d f
  disjoint F d
  disjoint f w
  disjoint F w
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
  disjoint s z
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K z
  disjoint M a
  disjoint M d
  disjoint R a
  disjoint R c
  disjoint R d
  disjoint R h
  disjoint R i
  disjoint R k
  disjoint R m
  disjoint R r
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R z
  disjoint H a
  disjoint H d
  disjoint H z
  assert |- ( ph -> ( <. ( M + 1 ) , K >. PolyAP H \/ ( K + 1 ) MonoAP H ) )

  proof
    wph
    cK
    cF
    cvdwm
    wbr
    #
    cM
    c1
    caddc
    co
    cK
    cop
    cH
    cvdwp
    wbr
    #
    cK
    c1
    caddc
    co
    #
    cH
    cvdwm
    wbr
    #
    wo
    #
    wph
    cF
    cR
    c1
    cW
    cfz
    co
    #
    cmap
    co
    #
    c1
    cV
    cfz
    co
    #
    cmap
    co
    #
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
    @8
    wral
    @0
    wph
    @7
    @6
    cF
    wf
    #
    @9
    wph
    vx
    vy
    cR
    cF
    cH
    cV
    cW
    vdwlem9.v
    vdwlem9.w
    vdw.r
    vdwlem9.h
    vdwlem9.f
    vdwlem4
    #
    @6
    @7
    cF
    cR
    @5
    cmap
    ovex
    c1
    cV
    cfz
    ovex
    #
    elmap
    sylibr
    vdwlem9.a
    @11
    @0
    vf
    cF
    @8
    @10
    cF
    cK
    cvdwm
    breq2
    rspcv
    sylc
    wph
    @0
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
    #
    cF
    ccnv
    vg
    cv
    #
    csn
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
    vg
    wex
    @4
    wph
    @6
    cF
    cK
    @7
    va
    vg
    vd
    @14
    wph
    cK
    wph
    cK
    c2
    cuz
    cfv
    wcel
    #
    cK
    cn
    wcel
    #
    vdwlem9.k
    cK
    eluz2nn
    syl
    #
    nnnn0d
    #
    @13
    vdwmc
    wph
    @21
    @4
    vg
    wph
    @20
    @4
    va
    vd
    cn
    cn
    wph
    @15
    cn
    wcel
    #
    @16
    cn
    wcel
    #
    wa
    #
    @20
    @4
    wph
    @28
    @20
    wa
    #
    wa
    #
    cM
    cK
    cop
    @18
    cvdwp
    wbr
    #
    @2
    @18
    cvdwm
    wbr
    #
    wo
    #
    @4
    @30
    @33
    vg
    @6
    wral
    #
    @18
    @6
    wcel
    #
    @33
    wph
    @34
    @29
    vdwlem9.g
    adantr
    @30
    @15
    cF
    cfv
    #
    @18
    @6
    @30
    @15
    @7
    wcel
    #
    @36
    @18
    wceq
    #
    @30
    @15
    @19
    wcel
    #
    @37
    @38
    wa
    #
    @30
    @17
    @19
    @15
    wph
    @28
    @20
    simprr
    #
    @30
    @23
    @26
    @27
    @15
    @17
    wcel
    wph
    @23
    @29
    @24
    adantr
    wph
    @26
    @27
    @20
    simprll
    #
    wph
    @26
    @27
    @20
    simprlr
    #
    @15
    @16
    cK
    vdwapid1
    syl3anc
    sseldd
    @30
    cF
    @7
    wfn
    #
    @39
    @40
    wb
    wph
    @44
    @29
    wph
    @12
    @44
    @13
    @7
    @6
    cF
    ffn
    syl
    adantr
    @7
    @18
    @15
    cF
    fniniseg
    syl
    mpbid
    #
    simprd
    #
    @30
    @7
    @6
    @15
    cF
    wph
    @12
    @29
    @13
    adantr
    @30
    @37
    @38
    @45
    simpld
    #
    ffvelrnd
    eqeltrrd
    #
    @33
    vg
    @6
    rsp
    sylc
    @30
    @33
    @1
    @32
    wo
    #
    @4
    @30
    @31
    @49
    @32
    @30
    vx
    vy
    @15
    @16
    cR
    cF
    @18
    cH
    cK
    cM
    cV
    cW
    wph
    cV
    cn
    wcel
    #
    @29
    vdwlem9.v
    adantr
    #
    wph
    cW
    cn
    wcel
    @29
    vdwlem9.w
    adantr
    #
    wph
    cR
    cfn
    wcel
    #
    @29
    vdw.r
    adantr
    #
    wph
    c1
    cW
    c2
    cV
    cmul
    co
    #
    cmul
    co
    #
    cfz
    co
    cR
    cH
    wf
    @29
    vdwlem9.h
    adantr
    #
    vdwlem9.f
    wph
    cM
    cn
    wcel
    @29
    vdwlem9.m
    adantr
    @30
    @35
    @5
    cR
    @18
    wf
    #
    @48
    @30
    @53
    @5
    cvv
    wcel
    @35
    @58
    wb
    @54
    c1
    cW
    cfz
    ovex
    #
    cR
    @5
    @18
    cfn
    cvv
    elmapg
    sylancl
    mpbid
    wph
    @22
    @29
    vdwlem9.k
    adantr
    @42
    @43
    @41
    vdwlem7
    @32
    @49
    wi
    @30
    @32
    @1
    olc
    a1i
    jaod
    @30
    @32
    @3
    @1
    @30
    @32
    @2
    vy
    @5
    vy
    cv
    #
    cW
    @15
    c1
    cmin
    co
    #
    cV
    caddc
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cH
    cfv
    #
    cmpt
    #
    cvdwm
    wbr
    @3
    @30
    @66
    @18
    @2
    cvdwm
    @30
    @36
    @66
    @18
    @30
    @37
    @36
    @66
    wceq
    @47
    vx
    @15
    vy
    @5
    @60
    cW
    vx
    cv
    #
    c1
    cmin
    co
    #
    cV
    caddc
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cH
    cfv
    #
    cmpt
    @66
    @7
    cF
    vx
    va
    weq
    #
    vy
    @5
    @72
    @65
    @73
    @71
    @64
    cH
    @73
    @70
    @63
    @60
    caddc
    @73
    @69
    @62
    cW
    cmul
    @73
    @68
    @61
    cV
    caddc
    @67
    @15
    c1
    cmin
    oveq1
    oveq1d
    oveq2d
    oveq2d
    fveq2d
    mpteq2dv
    vdwlem9.f
    vy
    @5
    @65
    @59
    mptex
    fvmpt
    syl
    @46
    eqtr3d
    breq2d
    @30
    vz
    cR
    cH
    @66
    @2
    @56
    @63
    cW
    @54
    @30
    cK
    cn0
    wcel
    #
    @2
    cn0
    wcel
    wph
    @74
    @29
    @25
    adantr
    cK
    peano2nn0
    syl
    @52
    @30
    cW
    @62
    @52
    @30
    @61
    cn0
    wcel
    #
    @50
    @62
    cn
    wcel
    @30
    @26
    @75
    @42
    @15
    nnm1nn0
    syl
    #
    @51
    @61
    cV
    nn0nnaddcl
    syl2anc
    nnmulcld
    @57
    @30
    @56
    cW
    @15
    cV
    caddc
    co
    #
    cmul
    co
    #
    cuz
    cfv
    #
    cW
    @63
    caddc
    co
    #
    cuz
    cfv
    @30
    @78
    cz
    wcel
    @56
    cz
    wcel
    #
    @78
    @56
    cle
    wbr
    #
    @56
    @79
    wcel
    @30
    @78
    @30
    cW
    @77
    @52
    @30
    @15
    cV
    @42
    @51
    nnaddcld
    #
    nnmulcld
    nnzd
    wph
    @81
    @29
    wph
    @56
    wph
    cW
    @55
    vdwlem9.w
    wph
    c2
    cn
    wcel
    @50
    @55
    cn
    wcel
    2nn
    vdwlem9.v
    c2
    cV
    nnmulcl
    sylancr
    #
    nnmulcld
    nnzd
    adantr
    @30
    @77
    @55
    cle
    wbr
    #
    @82
    @30
    @77
    cV
    cV
    caddc
    co
    @55
    cle
    @30
    @15
    cV
    cV
    @30
    @15
    @42
    nnred
    @30
    cV
    @51
    nnred
    #
    @86
    @30
    @37
    @15
    cV
    cle
    wbr
    @47
    @15
    c1
    cV
    elfzle2
    syl
    leadd1dd
    @30
    cV
    @30
    cV
    @51
    nncnd
    #
    2timesd
    breqtrrd
    @30
    @77
    cr
    wcel
    @55
    cr
    wcel
    #
    cW
    cr
    wcel
    cc0
    cW
    clt
    wbr
    @85
    @82
    wb
    @30
    @77
    @83
    nnred
    wph
    @88
    @29
    wph
    @55
    @84
    nnred
    adantr
    @30
    cW
    @52
    nnred
    @30
    cW
    @52
    nngt0d
    @77
    @55
    cW
    lemul2
    syl112anc
    mpbid
    @78
    @56
    eluz2
    syl3anbrc
    @30
    @78
    @80
    cuz
    @30
    cW
    c1
    @62
    caddc
    co
    #
    cmul
    co
    cW
    c1
    cmul
    co
    #
    @63
    caddc
    co
    @78
    @80
    @30
    cW
    c1
    @62
    @30
    cW
    @52
    nncnd
    #
    @30
    1cnd
    #
    @30
    @61
    cV
    @30
    @61
    @76
    nn0cnd
    #
    @87
    addcld
    adddid
    @30
    @89
    @77
    cW
    cmul
    @30
    c1
    @61
    caddc
    co
    #
    cV
    caddc
    co
    @89
    @77
    @30
    c1
    @61
    cV
    @92
    @93
    @87
    addassd
    @30
    @94
    @15
    cV
    caddc
    @30
    c1
    cc
    wcel
    @15
    cc
    wcel
    @94
    @15
    wceq
    ax-1cn
    @30
    @15
    @42
    nncnd
    c1
    @15
    pncan3
    sylancr
    oveq1d
    eqtr3d
    oveq2d
    @30
    @90
    cW
    @63
    caddc
    @30
    cW
    @91
    mulid1d
    oveq1d
    3eqtr3d
    fveq2d
    eleqtrd
    vy
    vz
    @5
    @65
    vz
    cv
    #
    @63
    caddc
    co
    #
    cH
    cfv
    vy
    vz
    weq
    @64
    @96
    cH
    @60
    @95
    @63
    caddc
    oveq1
    fveq2d
    cbvmptv
    vdwlem2
    sylbird
    orim2d
    syld
    mpd
    expr
    rexlimdvva
    exlimdv
    sylbid
    mpd
end
