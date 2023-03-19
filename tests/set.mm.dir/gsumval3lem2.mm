include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfz.mm"
include "crn.mm"
include "wcel.mm"
include "wn.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "co.mm"
include "clt.mm"
include "cv.mm"
include "wiso.mm"
include "csupp.mm"
include "wf1o.mm"
include "ccom.mm"
include "cseq.mm"
include "wceq.mm"
include "wex.mm"
include "cgsu.mm"
include "cvv.mm"
include "wf.mm"
include "cfn.mm"
include "wf1.mm"
include "f1f.mm"
include "syl.mm"
include "fzfid.mm"
include "fex2.mm"
include "syl3anc.mm"
include "vex.mm"
include "coexg.mm"
include "sylancl.mm"
include "ad2antrr.mm"
include "gsumval3lem1.mm"
include "cen.mm"
include "wbr.mm"
include "cres.mm"
include "resexg.mm"
include "cima.mm"
include "wss.mm"
include "cdm.mm"
include "suppssdm.mm"
include "eqsstri.mm"
include "fco.mm"
include "syl2anc.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "f1ores.mm"
include "wb.mm"
include "imaeq2i.mm"
include "wfun.mm"
include "fex.mm"
include "ovex.mm"
include "jca.mm"
include "f1fun.mm"
include "imacosupp.mm"
include "sylc.mm"
include "adantr.mm"
include "syl5eq.mm"
include "f1oeq3.mm"
include "mpbid.mm"
include "f1oen3g.mm"
include "fzfi.mm"
include "ssfi.mm"
include "sylancr.mm"
include "f1f1orn.mm"
include "enfi.mm"
include "mpbii.mm"
include "hashen.mm"
include "mpbird.mm"
include "fveq2d.mm"
include "f1oeq1.mm"
include "coeq2.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "wal.mm"
include "cio.mm"
include "weu.mm"
include "cmnd.mm"
include "neeq1i.mm"
include "wi.mm"
include "supp0cosupp0.mm"
include "necon3d.mm"
include "syl5bi.mm"
include "imp.mm"
include "frn.mm"
include "sstrd.mm"
include "gsumval3eu.mm"
include "iota1.mm"
include "eqid.mm"
include "simprl.mm"
include "gsumval3a.mm"
include "eqeq1d.mm"
include "bitr4d.mm"
include "alrimiv.mm"
include "fvex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "eqeq2.mm"
include "bibi12d.mm"
include "spcv.mm"

theorem gsumval3lem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gsumval3.b: |- B = ( Base ` G )
  assume gsumval3.0: |- .0. = ( 0g ` G )
  assume gsumval3.p: |- .+ = ( +g ` G )
  assume gsumval3.z: |- Z = ( Cntz ` G )
  assume gsumval3.g: |- ( ph -> G e. Mnd )
  assume gsumval3.a: |- ( ph -> A e. V )
  assume gsumval3.f: |- ( ph -> F : A --> B )
  assume gsumval3.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumval3.m: |- ( ph -> M e. NN )
  assume gsumval3.h: |- ( ph -> H : ( 1 ... M ) -1-1-> A )
  assume gsumval3.n: |- ( ph -> ( F supp .0. ) C_ ran H )
  assume gsumval3.w: |- W = ( ( F o. H ) supp .0. )

  disjoint .+ f
  disjoint A f
  disjoint f ph
  disjoint G f
  disjoint M f
  disjoint B f
  disjoint F f
  disjoint H f
  disjoint W f
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint .+ g
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint .+ k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint .+ m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint .+ n
  disjoint x y
  disjoint x z
  disjoint .+ x
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint A g
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint g ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .0. g
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  disjoint G g
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint V x
  disjoint B g
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F g
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint H g
  disjoint H k
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint W g
  disjoint W k
  disjoint W m
  disjoint W n
  disjoint W x
  disjoint W y
  disjoint W z
  assert |- ( ( ( ph /\ W =/= (/) ) /\ ( -. A e. ran ... /\ f Isom < , < ( ( 1 ... ( # ` W ) ) , W ) ) ) -> ( G gsum F ) = ( seq 1 ( .+ , ( F o. ( H o. f ) ) ) ` ( # ` W ) ) )

  proof
    wph
    cW
    c0
    wne
    #
    wa
    #
    cA
    cfz
    crn
    wcel
    wn
    #
    c1
    cW
    chash
    cfv
    #
    cfz
    co
    cW
    clt
    clt
    vf
    cv
    #
    wiso
    #
    wa
    #
    wa
    #
    c1
    cF
    c.0
    csupp
    co
    #
    chash
    cfv
    #
    cfz
    co
    #
    @8
    vg
    cv
    #
    wf1o
    #
    @3
    c.pl
    cF
    cH
    @4
    ccom
    #
    ccom
    #
    c1
    cseq
    #
    cfv
    #
    @9
    c.pl
    cF
    @11
    ccom
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vg
    wex
    #
    cG
    cF
    cgsu
    co
    #
    @16
    wceq
    #
    @7
    @13
    cvv
    wcel
    #
    @10
    @8
    @13
    wf1o
    #
    @16
    @9
    @15
    cfv
    #
    wceq
    #
    wa
    #
    @22
    wph
    @25
    @0
    @6
    wph
    cH
    cvv
    wcel
    #
    @4
    cvv
    wcel
    @25
    wph
    c1
    cM
    cfz
    co
    #
    cA
    cH
    wf
    #
    @31
    cfn
    wcel
    #
    cA
    cV
    wcel
    #
    @30
    wph
    @31
    cA
    cH
    wf1
    #
    @32
    gsumval3.h
    @31
    cA
    cH
    f1f
    syl
    #
    wph
    c1
    cM
    fzfid
    gsumval3.a
    @31
    cA
    cH
    cfn
    cV
    fex2
    syl3anc
    #
    vf
    vex
    cH
    @4
    cvv
    cvv
    coexg
    sylancl
    ad2antrr
    @7
    @26
    @28
    wph
    cA
    cB
    c.pl
    vf
    cF
    cG
    cH
    cM
    cV
    cW
    c.0
    cZ
    gsumval3.b
    gsumval3.0
    gsumval3.p
    gsumval3.z
    gsumval3.g
    gsumval3.a
    gsumval3.f
    gsumval3.c
    gsumval3.m
    gsumval3.h
    gsumval3.n
    gsumval3.w
    gsumval3lem1
    @7
    @3
    @9
    @15
    @7
    @3
    @9
    wceq
    #
    cW
    @8
    cen
    wbr
    #
    @7
    cH
    cW
    cres
    #
    cvv
    wcel
    #
    cW
    @8
    @40
    wf1o
    #
    @39
    wph
    @41
    @0
    @6
    wph
    @30
    @41
    @37
    cH
    cW
    cvv
    resexg
    syl
    ad2antrr
    @7
    cW
    cH
    cW
    cima
    #
    @40
    wf1o
    #
    @42
    @7
    @35
    cW
    @31
    wss
    #
    @44
    wph
    @35
    @0
    @6
    gsumval3.h
    ad2antrr
    wph
    @45
    @0
    @6
    wph
    cF
    cH
    ccom
    #
    cdm
    #
    cW
    @31
    cW
    @46
    c.0
    csupp
    co
    #
    @47
    gsumval3.w
    @46
    c.0
    suppssdm
    eqsstri
    wph
    @31
    cB
    @46
    wf
    #
    @47
    @31
    wceq
    wph
    cA
    cB
    cF
    wf
    #
    @32
    @49
    gsumval3.f
    @36
    @31
    cA
    cB
    cF
    cH
    fco
    syl2anc
    @31
    cB
    @46
    fdm
    syl
    syl5sseq
    #
    ad2antrr
    @31
    cA
    cW
    cH
    f1ores
    syl2anc
    @7
    @43
    @8
    wceq
    #
    @44
    @42
    wb
    @1
    @52
    @6
    @1
    @43
    cH
    @48
    cima
    #
    @8
    cW
    @48
    cH
    gsumval3.w
    imaeq2i
    wph
    @53
    @8
    wceq
    #
    @0
    wph
    cF
    cvv
    wcel
    #
    @30
    wa
    #
    cH
    wfun
    #
    @8
    cH
    crn
    #
    wss
    #
    wa
    @54
    wph
    @55
    @30
    wph
    @50
    @34
    @55
    gsumval3.f
    gsumval3.a
    cA
    cB
    cV
    cF
    fex
    syl2anc
    #
    wph
    @32
    @31
    cvv
    wcel
    @30
    @36
    c1
    cM
    cfz
    ovex
    @31
    cA
    cvv
    cH
    fex
    sylancl
    #
    jca
    wph
    @57
    @59
    wph
    @35
    @57
    gsumval3.h
    @31
    cA
    cH
    f1fun
    syl
    gsumval3.n
    jca
    cF
    cH
    cvv
    cvv
    c.0
    imacosupp
    sylc
    adantr
    syl5eq
    adantr
    @43
    @8
    cW
    @40
    f1oeq3
    syl
    mpbid
    cW
    @8
    @40
    cvv
    f1oen3g
    syl2anc
    @7
    cW
    cfn
    wcel
    #
    @8
    cfn
    wcel
    #
    @38
    @39
    wb
    wph
    @62
    @0
    @6
    wph
    @33
    @45
    @62
    c1
    cM
    fzfi
    #
    @51
    @31
    cW
    ssfi
    sylancr
    ad2antrr
    wph
    @63
    @0
    @6
    wph
    @58
    cfn
    wcel
    #
    @59
    @63
    wph
    @33
    @65
    @64
    wph
    @31
    @58
    cen
    wbr
    #
    @33
    @65
    wb
    wph
    @30
    @31
    @58
    cH
    wf1o
    #
    @66
    @37
    wph
    @35
    @67
    gsumval3.h
    @31
    cA
    cH
    f1f1orn
    syl
    @31
    @58
    cH
    cvv
    f1oen3g
    syl2anc
    @31
    @58
    enfi
    syl
    mpbii
    gsumval3.n
    @58
    @8
    ssfi
    syl2anc
    ad2antrr
    #
    cW
    @8
    hashen
    syl2anc
    mpbird
    fveq2d
    jca
    @21
    @29
    vg
    @13
    cvv
    @11
    @13
    wceq
    #
    @12
    @26
    @20
    @28
    @10
    @8
    @11
    @13
    f1oeq1
    @69
    @19
    @27
    @16
    @69
    @9
    @18
    @15
    @69
    @17
    @14
    c.pl
    c1
    @11
    @13
    cF
    coeq2
    seqeq3d
    fveq1d
    eqeq2d
    anbi12d
    spcegv
    sylc
    @7
    @12
    vx
    cv
    #
    @19
    wceq
    #
    wa
    #
    vg
    wex
    #
    @23
    @70
    wceq
    #
    wb
    #
    vx
    wal
    @22
    @24
    wb
    #
    @7
    @75
    vx
    @7
    @73
    @73
    vx
    cio
    #
    @70
    wceq
    #
    @74
    @7
    @73
    vx
    weu
    @73
    @78
    wb
    @7
    vx
    cA
    cB
    c.pl
    vg
    cF
    cG
    cV
    @8
    c.0
    cZ
    gsumval3.b
    gsumval3.0
    gsumval3.p
    gsumval3.z
    wph
    cG
    cmnd
    wcel
    @0
    @6
    gsumval3.g
    ad2antrr
    #
    wph
    @34
    @0
    @6
    gsumval3.a
    ad2antrr
    #
    wph
    @50
    @0
    @6
    gsumval3.f
    ad2antrr
    #
    wph
    cF
    crn
    #
    @82
    cZ
    cfv
    wss
    @0
    @6
    gsumval3.c
    ad2antrr
    #
    @68
    @1
    @8
    c0
    wne
    #
    @6
    wph
    @0
    @84
    @0
    @48
    c0
    wne
    #
    wph
    @84
    cW
    @48
    c0
    gsumval3.w
    neeq1i
    wph
    @55
    @30
    @85
    @84
    wi
    @60
    @61
    @56
    @8
    c0
    @48
    c0
    cF
    cH
    cvv
    cvv
    c.0
    supp0cosupp0
    necon3d
    syl2anc
    syl5bi
    imp
    adantr
    #
    @7
    @8
    @58
    cA
    wph
    @59
    @0
    @6
    gsumval3.n
    ad2antrr
    wph
    @58
    cA
    wss
    #
    @0
    @6
    wph
    @32
    @87
    @36
    @31
    cA
    cH
    frn
    syl
    ad2antrr
    sstrd
    gsumval3eu
    @73
    vx
    iota1
    syl
    @7
    @23
    @77
    @70
    @7
    vx
    cA
    cB
    c.pl
    vg
    cF
    cG
    cV
    @8
    c.0
    cZ
    gsumval3.b
    gsumval3.0
    gsumval3.p
    gsumval3.z
    @79
    @80
    @81
    @83
    @68
    @86
    @8
    eqid
    @1
    @2
    @5
    simprl
    gsumval3a
    eqeq1d
    bitr4d
    alrimiv
    @75
    @76
    vx
    @16
    @3
    @15
    fvex
    @70
    @16
    wceq
    #
    @73
    @22
    @74
    @24
    @88
    @72
    @21
    vg
    @88
    @71
    @20
    @12
    @70
    @16
    @19
    eqeq1
    anbi2d
    exbidv
    @70
    @16
    @23
    eqeq2
    bibi12d
    spcv
    syl
    mpbid
end
