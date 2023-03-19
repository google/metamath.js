include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wss.mm"
include "co.mm"
include "cmpt.mm"
include "cres.mm"
include "cgsu.mm"
include "crn.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "wrex.mm"
include "wex.mm"
include "elfpw.mm"
include "simprbi.mm"
include "syl.mm"
include "simplbi.mm"
include "sselda.mm"
include "eqid.mm"
include "ccmn.mm"
include "adantr.mm"
include "ctps.mm"
include "ctgp.mm"
include "tgptps.mm"
include "fovrn.mm"
include "syl3an1.mm"
include "3expa.mm"
include "fmptd.mm"
include "cima.mm"
include "df-ima.mm"
include "ctopon.mm"
include "tgptopon.mm"
include "toponss.mm"
include "syl2anc.mm"
include "resmptd.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "chmeo.mm"
include "cminusg.mm"
include "ccom.mm"
include "wceq.mm"
include "ffvelrnda.mm"
include "grpsubval.mm"
include "sylan.mm"
include "mpteq2dva.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "grpinvcl.mm"
include "grpinvf.mm"
include "feqmptd.mm"
include "eqidd.mm"
include "oveq2.mm"
include "fmptco.mm"
include "eqtr4d.mm"
include "grpinvhmeo.mm"
include "tgplacthmeo.mm"
include "hmeoco.mm"
include "eqeltrd.mm"
include "hmeoima.mm"
include "eqeltrrd.mm"
include "grpsubid1.mm"
include "cvv.mm"
include "ovex.mm"
include "elrnmpt1s.mm"
include "sylancl.mm"
include "tsmsi.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "sseq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "ac6sfi.mm"
include "cuni.mm"
include "cun.mm"
include "frn.mm"
include "adantl.mm"
include "inss1.mm"
include "syl6ss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "rnss.mm"
include "3syl.mm"
include "rnxpss.mm"
include "unssd.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "fofi.mm"
include "inss2.mm"
include "unifi.mm"
include "rnfi.mm"
include "unfi.mm"
include "sylanbrc.mm"
include "adantrr.mm"
include "ssun2.mm"
include "a1i.mm"
include "adantlr.mm"
include "wb.mm"
include "fvssunirn.mm"
include "ssun1.mm"
include "sstri.mm"
include "id.mm"
include "syl5sseqr.mm"
include "pm5.5.mm"
include "reseq2.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "bitrd.mm"
include "rspcv.mm"
include "cmnd.mm"
include "ad2antrr.mm"
include "cmnmnd.mm"
include "simplr.mm"
include "jca.mm"
include "ovexd.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fsuppmptdm.mm"
include "gsumcl.mm"
include "weq.mm"
include "velsn.mm"
include "ovres.mm"
include "sylanbr.mm"
include "oveq1.mm"
include "eqtrd.mm"
include "gsumsn.mm"
include "syl3anc.mm"
include "snfi.mm"
include "snssd.mm"
include "xpss12.mm"
include "fssresd.mm"
include "xpfi.mm"
include "sylancr.mm"
include "fdmfifsupp.mm"
include "gsumxp.mm"
include "3eqtr4rd.mm"
include "elrnmpti.mm"
include "cabl.mm"
include "isabl.mm"
include "ad3antrrr.mm"
include "ablnncan.mm"
include "simpr.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "syld.mm"
include "an32s.mm"
include "ralimdva.mm"
include "impr.mm"
include "fveq2.mm"
include "sneq.mm"
include "xpeq1d.mm"
include "reseq2d.mm"
include "oveq12d.mm"
include "cbvralv.mm"
include "sseq2.mm"
include "xpeq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "exlimddv.mm"

theorem tsmsxplem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vg: setvar g
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vh: setvar h
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let cS: class S
  let cN: class N
  let cU: class U
  let cT: class T
  assume tsmsxp.b: |- B = ( Base ` G )
  assume tsmsxp.g: |- ( ph -> G e. CMnd )
  assume tsmsxp.2: |- ( ph -> G e. TopGrp )
  assume tsmsxp.a: |- ( ph -> A e. V )
  assume tsmsxp.c: |- ( ph -> C e. W )
  assume tsmsxp.f: |- ( ph -> F : ( A X. C ) --> B )
  assume tsmsxp.h: |- ( ph -> H : A --> B )
  assume tsmsxp.1: |- ( ( ph /\ j e. A ) -> ( H ` j ) e. ( G tsums ( k e. C |-> ( j F k ) ) ) )
  assume tsmsxp.j: |- J = ( TopOpen ` G )
  assume tsmsxp.z: |- .0. = ( 0g ` G )
  assume tsmsxp.p: |- .+ = ( +g ` G )
  assume tsmsxp.m: |- .- = ( -g ` G )
  assume tsmsxp.l: |- ( ph -> L e. J )
  assume tsmsxp.3: |- ( ph -> .0. e. L )
  assume tsmsxp.k: |- ( ph -> K e. ( ~P A i^i Fin ) )
  assume tsmsxp.ks: |- ( ph -> dom D C_ K )
  assume tsmsxp.d: |- ( ph -> D e. ( ~P ( A X. C ) i^i Fin ) )

  disjoint .0. k
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint G j
  disjoint k n
  disjoint k x
  disjoint G k
  disjoint n x
  disjoint G n
  disjoint G x
  disjoint B k
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D x
  disjoint L j
  disjoint L n
  disjoint L x
  disjoint A j
  disjoint A k
  disjoint A n
  disjoint K j
  disjoint K k
  disjoint K n
  disjoint K x
  disjoint H j
  disjoint H k
  disjoint H n
  disjoint H x
  disjoint .- j
  disjoint .- n
  disjoint .- x
  disjoint C j
  disjoint C k
  disjoint C n
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint F x
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint g k
  disjoint g w
  disjoint g y
  disjoint g z
  disjoint .0. g
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint w y
  disjoint w z
  disjoint .0. w
  disjoint y z
  disjoint .0. y
  disjoint .0. z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint G a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b j
  disjoint b k
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint G b
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c j
  disjoint c k
  disjoint c n
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint G c
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d j
  disjoint d k
  disjoint d n
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint G d
  disjoint f g
  disjoint f h
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint g h
  disjoint g j
  disjoint g n
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint G g
  disjoint h j
  disjoint h k
  disjoint h n
  disjoint h s
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint G h
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j y
  disjoint j z
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint G t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint w x
  disjoint G w
  disjoint x y
  disjoint x z
  disjoint G y
  disjoint G z
  disjoint J y
  disjoint B b
  disjoint B g
  disjoint B h
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint D f
  disjoint D g
  disjoint D y
  disjoint D z
  disjoint L f
  disjoint L g
  disjoint L y
  disjoint L z
  disjoint A a
  disjoint A b
  disjoint A g
  disjoint A h
  disjoint A s
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A y
  disjoint A z
  disjoint K c
  disjoint K d
  disjoint K f
  disjoint K g
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint S c
  disjoint H a
  disjoint H b
  disjoint H d
  disjoint H f
  disjoint H g
  disjoint H h
  disjoint H s
  disjoint H t
  disjoint H u
  disjoint H v
  disjoint H y
  disjoint H z
  disjoint N c
  disjoint N d
  disjoint N g
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint U c
  disjoint U d
  disjoint .- d
  disjoint .- f
  disjoint .- g
  disjoint .- y
  disjoint .- z
  disjoint C b
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint C z
  disjoint T c
  disjoint T d
  disjoint T g
  disjoint .+ c
  disjoint .+ d
  disjoint .+ g
  disjoint .+ y
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> E. n e. ( ~P C i^i Fin ) ( ran D C_ n /\ A. x e. K ( ( H ` x ) .- ( G gsum ( F |` ( { x } X. n ) ) ) ) e. L ) )

  proof
    wph
    cK
    cC
    cpw
    #
    cfn
    cin
    #
    vf
    cv
    #
    wf
    #
    vj
    cv
    #
    @2
    cfv
    #
    vz
    cv
    #
    wss
    #
    cG
    vk
    cC
    @4
    vk
    cv
    #
    cF
    co
    #
    cmpt
    #
    @6
    cres
    #
    cgsu
    co
    #
    vg
    cL
    @4
    cH
    cfv
    #
    vg
    cv
    #
    c.mi
    co
    #
    cmpt
    #
    crn
    #
    wcel
    #
    wi
    #
    vz
    @1
    wral
    #
    vj
    cK
    wral
    #
    wa
    #
    cD
    crn
    #
    vn
    cv
    #
    wss
    #
    vx
    cv
    #
    cH
    cfv
    #
    cG
    cF
    @26
    csn
    #
    @24
    cxp
    #
    cres
    #
    cgsu
    co
    #
    c.mi
    co
    #
    cL
    wcel
    #
    vx
    cK
    wral
    #
    wa
    #
    vn
    @1
    wrex
    #
    vf
    wph
    cK
    cfn
    wcel
    #
    vy
    cv
    #
    @6
    wss
    #
    @18
    wi
    #
    vz
    @1
    wral
    #
    vy
    @1
    wrex
    #
    vj
    cK
    wral
    @22
    vf
    wex
    wph
    cK
    cA
    cpw
    cfn
    cin
    wcel
    #
    @37
    tsmsxp.k
    @43
    cK
    cA
    wss
    #
    @37
    cK
    cA
    elfpw
    #
    simprbi
    syl
    #
    wph
    @42
    vj
    cK
    wph
    @4
    cK
    wcel
    #
    @4
    cA
    wcel
    #
    @42
    wph
    cK
    cA
    @4
    wph
    @43
    @44
    tsmsxp.k
    @43
    @44
    @37
    @45
    simplbi
    syl
    sselda
    #
    wph
    @48
    wa
    #
    vz
    vy
    cC
    cB
    @13
    @1
    @17
    @10
    cG
    cJ
    cW
    tsmsxp.b
    tsmsxp.j
    @1
    eqid
    wph
    cG
    ccmn
    wcel
    #
    @48
    tsmsxp.g
    adantr
    wph
    cG
    ctps
    wcel
    #
    @48
    wph
    cG
    ctgp
    wcel
    #
    @52
    tsmsxp.2
    cG
    tgptps
    syl
    adantr
    wph
    cC
    cW
    wcel
    @48
    tsmsxp.c
    adantr
    @50
    vk
    cC
    @9
    cB
    @10
    wph
    @48
    @8
    cC
    wcel
    #
    @9
    cB
    wcel
    #
    wph
    cA
    cC
    cxp
    #
    cB
    cF
    wf
    #
    @48
    @54
    @55
    tsmsxp.f
    @4
    @8
    cB
    cA
    cC
    cF
    fovrn
    #
    syl3an1
    3expa
    @10
    eqid
    fmptd
    tsmsxp.1
    @50
    vg
    cB
    @15
    cmpt
    #
    cL
    cima
    #
    @17
    cJ
    @50
    @60
    @59
    cL
    cres
    #
    crn
    @17
    @59
    cL
    df-ima
    @50
    @61
    @16
    @50
    vg
    cB
    cL
    @15
    wph
    cL
    cB
    wss
    #
    @48
    wph
    cJ
    cB
    ctopon
    cfv
    wcel
    #
    cL
    cJ
    wcel
    #
    @62
    wph
    @53
    @63
    tsmsxp.2
    cG
    cJ
    cB
    tsmsxp.j
    tsmsxp.b
    tgptopon
    syl
    tsmsxp.l
    cL
    cJ
    cB
    toponss
    syl2anc
    #
    adantr
    resmptd
    rneqd
    syl5eq
    @50
    @59
    cJ
    cJ
    chmeo
    co
    #
    wcel
    @64
    @60
    cJ
    wcel
    @50
    @59
    vy
    cB
    @13
    @38
    c.pl
    co
    #
    cmpt
    #
    cG
    cminusg
    cfv
    #
    ccom
    #
    @66
    @50
    @59
    vg
    cB
    @13
    @14
    @69
    cfv
    #
    c.pl
    co
    #
    cmpt
    @70
    @50
    vg
    cB
    @15
    @72
    @50
    @13
    cB
    wcel
    #
    @14
    cB
    wcel
    #
    @15
    @72
    wceq
    wph
    cA
    cB
    @4
    cH
    tsmsxp.h
    ffvelrnda
    #
    cB
    c.pl
    cG
    @69
    c.mi
    @13
    @14
    tsmsxp.b
    tsmsxp.p
    @69
    eqid
    #
    tsmsxp.m
    grpsubval
    sylan
    mpteq2dva
    @50
    vg
    vy
    cB
    cB
    @71
    @67
    @72
    @69
    @68
    @50
    cG
    cgrp
    wcel
    #
    @74
    @71
    cB
    wcel
    wph
    @77
    @48
    wph
    @53
    @77
    tsmsxp.2
    cG
    tgpgrp
    syl
    #
    adantr
    #
    cB
    cG
    @69
    @14
    tsmsxp.b
    @76
    grpinvcl
    sylan
    @50
    vg
    cB
    cB
    @69
    @50
    @77
    cB
    cB
    @69
    wf
    @79
    cB
    cG
    @69
    tsmsxp.b
    @76
    grpinvf
    syl
    feqmptd
    @50
    @68
    eqidd
    @38
    @71
    @13
    c.pl
    oveq2
    fmptco
    eqtr4d
    @50
    @69
    @66
    wcel
    #
    @68
    @66
    wcel
    #
    @70
    @66
    wcel
    @50
    @53
    @80
    wph
    @53
    @48
    tsmsxp.2
    adantr
    #
    cG
    @69
    cJ
    tsmsxp.j
    @76
    grpinvhmeo
    syl
    @50
    @53
    @73
    @81
    @82
    @75
    vy
    @13
    c.pl
    @68
    cG
    cJ
    cB
    @68
    eqid
    tsmsxp.b
    tsmsxp.p
    tsmsxp.j
    tgplacthmeo
    syl2anc
    @69
    @68
    cJ
    cJ
    cJ
    hmeoco
    syl2anc
    eqeltrd
    wph
    @64
    @48
    tsmsxp.l
    adantr
    cL
    @59
    cJ
    cJ
    hmeoima
    syl2anc
    eqeltrrd
    @50
    @13
    c.0
    c.mi
    co
    #
    @13
    @17
    @50
    @77
    @73
    @83
    @13
    wceq
    @79
    @75
    cB
    cG
    c.mi
    @13
    c.0
    tsmsxp.b
    tsmsxp.z
    tsmsxp.m
    grpsubid1
    syl2anc
    @50
    c.0
    cL
    wcel
    #
    @83
    cvv
    wcel
    @83
    @17
    wcel
    wph
    @84
    @48
    tsmsxp.3
    adantr
    @13
    c.0
    c.mi
    ovex
    vg
    cL
    @15
    @83
    c.0
    @16
    cvv
    @16
    eqid
    #
    @14
    c.0
    @13
    c.mi
    oveq2
    elrnmpt1s
    sylancl
    eqeltrrd
    tsmsi
    syldan
    ralrimiva
    @41
    @20
    vj
    vy
    cK
    @1
    vf
    @38
    @5
    wceq
    #
    @40
    @19
    vz
    @1
    @86
    @39
    @7
    @18
    @38
    @5
    @6
    sseq1
    imbi1d
    ralbidv
    ac6sfi
    syl2anc
    wph
    @22
    wa
    #
    @2
    crn
    #
    cuni
    #
    @23
    cun
    #
    @1
    wcel
    #
    @23
    @90
    wss
    #
    @27
    cG
    cF
    @28
    @90
    cxp
    #
    cres
    #
    cgsu
    co
    #
    c.mi
    co
    #
    cL
    wcel
    #
    vx
    cK
    wral
    #
    @36
    wph
    @3
    @91
    @21
    wph
    @3
    wa
    #
    @90
    cC
    wss
    #
    @90
    cfn
    wcel
    #
    @91
    @99
    @89
    @23
    cC
    @99
    @88
    @0
    wss
    @89
    cC
    wss
    @99
    @88
    @1
    @0
    @3
    @88
    @1
    wss
    wph
    cK
    @1
    @2
    frn
    adantl
    #
    @0
    cfn
    inss1
    syl6ss
    @88
    cC
    sspwuni
    sylib
    wph
    @23
    cC
    wss
    @3
    wph
    @23
    @56
    crn
    #
    cC
    wph
    cD
    @56
    cpw
    cfn
    cin
    wcel
    #
    cD
    @56
    wss
    #
    @23
    @103
    wss
    tsmsxp.d
    @104
    @105
    cD
    cfn
    wcel
    #
    cD
    @56
    elfpw
    #
    simplbi
    cD
    @56
    rnss
    3syl
    cA
    cC
    rnxpss
    syl6ss
    adantr
    unssd
    #
    @99
    @89
    cfn
    wcel
    #
    @23
    cfn
    wcel
    #
    @101
    @99
    @88
    cfn
    wcel
    #
    @88
    cfn
    wss
    @109
    @99
    @37
    cK
    @88
    @2
    wfo
    #
    @111
    wph
    @37
    @3
    @46
    adantr
    @99
    @2
    cK
    wfn
    #
    @112
    @3
    @113
    wph
    cK
    @1
    @2
    ffn
    adantl
    cK
    @2
    dffn4
    sylib
    cK
    @88
    @2
    fofi
    syl2anc
    @99
    @88
    @1
    cfn
    @102
    @0
    cfn
    inss2
    syl6ss
    @88
    unifi
    syl2anc
    wph
    @110
    @3
    wph
    @104
    @106
    @110
    tsmsxp.d
    @104
    @105
    @106
    @107
    simprbi
    cD
    rnfi
    3syl
    adantr
    @89
    @23
    unfi
    syl2anc
    #
    @90
    cC
    elfpw
    sylanbrc
    #
    adantrr
    @92
    @87
    @23
    @89
    ssun2
    a1i
    @87
    @13
    cG
    cF
    @4
    csn
    #
    @90
    cxp
    #
    cres
    #
    cgsu
    co
    #
    c.mi
    co
    #
    cL
    wcel
    #
    vj
    cK
    wral
    #
    @98
    wph
    @3
    @21
    @122
    @99
    @20
    @121
    vj
    cK
    wph
    @47
    @3
    @20
    @121
    wi
    wph
    @47
    wa
    #
    @3
    wa
    #
    @20
    cG
    @10
    @90
    cres
    #
    cgsu
    co
    #
    @17
    wcel
    #
    @121
    @124
    @91
    @20
    @127
    wi
    wph
    @3
    @91
    @47
    @115
    adantlr
    @19
    @127
    vz
    @90
    @1
    @6
    @90
    wceq
    #
    @19
    @18
    @127
    @128
    @7
    @19
    @18
    wb
    @128
    @90
    @5
    @6
    @5
    @89
    @90
    @2
    @4
    fvssunirn
    @89
    @23
    ssun1
    sstri
    @128
    id
    syl5sseqr
    @7
    @18
    pm5.5
    syl
    @128
    @12
    @126
    @17
    @128
    @11
    @125
    cG
    cgsu
    @6
    @90
    @10
    reseq2
    oveq2d
    eleq1d
    bitrd
    rspcv
    syl
    @124
    @127
    @119
    @17
    wcel
    #
    @121
    @124
    @126
    @119
    @17
    @124
    cG
    vy
    @116
    cG
    vk
    @90
    @38
    @8
    @118
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    cgsu
    co
    #
    cG
    vk
    @90
    @9
    cmpt
    #
    cgsu
    co
    #
    @119
    @126
    @124
    cG
    cmnd
    wcel
    #
    @47
    @135
    cB
    wcel
    @133
    @135
    wceq
    @124
    @51
    @136
    wph
    @51
    @47
    @3
    tsmsxp.g
    ad2antrr
    #
    cG
    cmnmnd
    syl
    wph
    @47
    @3
    simplr
    @124
    @90
    cB
    @134
    cG
    cfn
    c.0
    tsmsxp.b
    tsmsxp.z
    @137
    wph
    @3
    @101
    @47
    @114
    adantlr
    #
    @124
    vk
    @90
    @9
    cB
    @134
    @124
    @8
    @90
    wcel
    #
    @54
    @55
    @124
    @90
    cC
    @8
    wph
    @3
    @100
    @47
    @108
    adantlr
    #
    sselda
    @123
    @54
    @55
    @3
    @123
    @57
    @48
    wa
    @54
    @55
    @123
    @57
    @48
    wph
    @57
    @47
    tsmsxp.f
    adantr
    @49
    jca
    @57
    @48
    @54
    @55
    @58
    3expa
    sylan
    adantlr
    syldan
    @134
    eqid
    #
    fmptd
    @124
    vk
    @90
    @134
    cvv
    cvv
    @9
    c.0
    @141
    @138
    @124
    @139
    wa
    @4
    @8
    cF
    ovexd
    c.0
    cvv
    wcel
    @124
    c.0
    cG
    c0g
    cfv
    cvv
    tsmsxp.z
    cG
    c0g
    fvex
    eqeltri
    a1i
    #
    fsuppmptdm
    gsumcl
    @132
    cB
    @135
    vy
    cG
    @4
    cK
    tsmsxp.b
    vy
    vj
    weq
    #
    @131
    @134
    cG
    cgsu
    @143
    vk
    @90
    @130
    @9
    @143
    @139
    wa
    @130
    @38
    @8
    cF
    co
    #
    @9
    @143
    @38
    @116
    wcel
    @139
    @130
    @144
    wceq
    vy
    @4
    velsn
    @38
    @8
    @116
    @90
    cF
    ovres
    sylanbr
    @143
    @144
    @9
    wceq
    @139
    @38
    @4
    @8
    cF
    oveq1
    adantr
    eqtrd
    mpteq2dva
    oveq2d
    gsumsn
    syl3anc
    @124
    @116
    cB
    @90
    vy
    vk
    @118
    cG
    cfn
    cfn
    c.0
    tsmsxp.b
    tsmsxp.z
    @137
    @116
    cfn
    wcel
    #
    @124
    @4
    snfi
    #
    a1i
    @138
    @124
    @56
    cB
    @117
    cF
    wph
    @57
    @47
    @3
    tsmsxp.f
    ad2antrr
    @124
    @116
    cA
    wss
    @100
    @117
    @56
    wss
    @124
    @4
    cA
    @123
    @48
    @3
    @49
    adantr
    snssd
    @140
    @116
    cA
    @90
    cC
    xpss12
    syl2anc
    fssresd
    #
    @124
    @117
    cB
    @118
    cvv
    c.0
    @147
    @124
    @145
    @101
    @117
    cfn
    wcel
    @146
    @138
    @116
    @90
    xpfi
    sylancr
    @142
    fdmfifsupp
    gsumxp
    @124
    @125
    @134
    cG
    cgsu
    @124
    vk
    cC
    @90
    @9
    @140
    resmptd
    oveq2d
    3eqtr4rd
    eleq1d
    @129
    @119
    @15
    wceq
    #
    vg
    cL
    wrex
    @124
    @121
    vg
    cL
    @15
    @119
    @16
    @85
    @13
    @14
    c.mi
    ovex
    elrnmpti
    @124
    @148
    @121
    vg
    cL
    @124
    @14
    cL
    wcel
    #
    wa
    #
    @121
    @148
    @13
    @15
    c.mi
    co
    #
    cL
    wcel
    @150
    @151
    @14
    cL
    @150
    cB
    cG
    c.mi
    @13
    @14
    tsmsxp.b
    tsmsxp.m
    wph
    cG
    cabl
    wcel
    #
    @47
    @3
    @149
    wph
    @77
    @51
    @152
    @78
    tsmsxp.g
    cG
    isabl
    sylanbrc
    ad3antrrr
    @123
    @73
    @3
    @149
    wph
    @47
    @48
    @73
    @49
    @75
    syldan
    ad2antrr
    @124
    cL
    cB
    @14
    wph
    @62
    @47
    @3
    @65
    ad2antrr
    sselda
    ablnncan
    @124
    @149
    simpr
    eqeltrd
    @148
    @120
    @151
    cL
    @119
    @15
    @13
    c.mi
    oveq2
    eleq1d
    syl5ibrcom
    rexlimdva
    syl5bi
    sylbid
    syld
    an32s
    ralimdva
    impr
    @121
    @97
    vj
    vx
    cK
    vj
    vx
    weq
    #
    @120
    @96
    cL
    @153
    @13
    @27
    @119
    @95
    c.mi
    @4
    @26
    cH
    fveq2
    @153
    @118
    @94
    cG
    cgsu
    @153
    @117
    @93
    cF
    @153
    @116
    @28
    @90
    @4
    @26
    sneq
    xpeq1d
    reseq2d
    oveq2d
    oveq12d
    eleq1d
    cbvralv
    sylib
    @35
    @92
    @98
    wa
    vn
    @90
    @1
    @24
    @90
    wceq
    #
    @25
    @92
    @34
    @98
    @24
    @90
    @23
    sseq2
    @154
    @33
    @97
    vx
    cK
    @154
    @32
    @96
    cL
    @154
    @31
    @95
    @27
    c.mi
    @154
    @30
    @94
    cG
    cgsu
    @154
    @29
    @93
    cF
    @24
    @90
    @28
    xpeq2
    reseq2d
    oveq2d
    oveq2d
    eleq1d
    ralbidv
    anbi12d
    rspcev
    syl12anc
    exlimddv
end
