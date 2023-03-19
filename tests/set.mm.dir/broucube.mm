include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cmpt.mm"
include "c1.mm"
include "cfz.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "wrex.mm"
include "crest.mm"
include "ccn.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "wfn.mm"
include "cicc.mm"
include "cmap.mm"
include "elmapfn.mm"
include "eleq2s.mm"
include "adantl.mm"
include "wf.mm"
include "cr.mm"
include "ctopon.mm"
include "wss.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ovex.mm"
include "retopon.mm"
include "pttoponconst.mm"
include "mp2an.mm"
include "reex.mm"
include "unitssre.mm"
include "mapss.mm"
include "eqsstri.mm"
include "resttopon.mm"
include "toponunii.mm"
include "cnf.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "ovexd.mm"
include "inidm.mm"
include "eqidd.mm"
include "offval.mm"
include "mpteq2dva.mm"
include "a1i.mm"
include "ctop.mm"
include "retop.mm"
include "fconst6.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "cnfldtop.mm"
include "cnrest2r.mm"
include "ax-mp.mm"
include "cres.mm"
include "resmpt.mm"
include "ptpjcn.mm"
include "mp3an12.mm"
include "cnrest.mm"
include "sylancl.mm"
include "syl5eqelr.mm"
include "fvex.mm"
include "fvconst2.mm"
include "tgioo2.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "sseldi.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "adantr.mm"
include "fveq1.mm"
include "cbvmptv.mm"
include "cnmpt11.mm"
include "ctx.mm"
include "subcn.mm"
include "cnmpt12f.mm"
include "wb.mm"
include "elmapi.mm"
include "adantll.mm"
include "resubcld.mm"
include "an32s.mm"
include "fmptd.mm"
include "frn.mm"
include "cc.mm"
include "cnfldtopon.mm"
include "ax-resscn.mm"
include "cnrest2.mm"
include "mp3an13.mm"
include "3syl.mm"
include "mpbid.mm"
include "eleqtrrd.mm"
include "ptcn.mm"
include "eqeltrd.mm"
include "w3a.mm"
include "cneg.mm"
include "cle.mm"
include "simpr2.mm"
include "weq.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fvmpt.mm"
include "fveq1d.mm"
include "adantlr.mm"
include "simpllr.mm"
include "ofval.mm"
include "df-neg.mm"
include "syl6eqr.mm"
include "exp41.mm"
include "com24.mm"
include "3imp2.mm"
include "eqtrd.mm"
include "wbr.mm"
include "cxr.mm"
include "0xr.mm"
include "1re.mm"
include "rexri.mm"
include "iccgelb.mm"
include "le0neg2d.mm"
include "anasss.mm"
include "3adantr3.mm"
include "eqbrtrd.mm"
include "iccleub.mm"
include "1red.mm"
include "subge0d.mm"
include "mpbird.mm"
include "breqtrrd.mm"
include "poimir.mm"
include "eqeq1d.mm"
include "wral.mm"
include "c0ex.mm"
include "eqeq12d.mm"
include "sstri.mm"
include "subeq0ad.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "offn.mm"
include "fnconstg.mm"
include "eqfnfv.mm"
include "syl2anc.mm"
include "3bitr4d.mm"
include "rexbidva.mm"

theorem broucube
  let wph: wff ph
  let cR: class R
  let cF: class F
  let cI: class I
  let cN: class N
  let vc: setvar c
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cT: class T
  let cU: class U
  let cV: class V
  let cB: class B
  let cK: class K
  let cC: class C
  let vg: setvar g
  let vr: setvar r
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let cG: class G
  let cX: class X
  assume poimir.0: |- ( ph -> N e. NN )
  assume poimir.i: |- I = ( ( 0 [,] 1 ) ^m ( 1 ... N ) )
  assume poimir.r: |- R = ( Xt_ ` ( ( 1 ... N ) X. { ( topGen ` ran (,) ) } ) )
  assume broucube.1: |- ( ph -> F e. ( ( R |`t I ) Cn ( R |`t I ) ) )

  disjoint c ph
  disjoint F c
  disjoint I c
  disjoint N c
  disjoint R c
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f p
  disjoint f q
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i p
  disjoint i q
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j p
  disjoint j q
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m p
  disjoint m q
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n p
  disjoint n q
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p q
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q s
  disjoint q t
  disjoint q u
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint j ph
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint F j
  disjoint F m
  disjoint F n
  disjoint F y
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M y
  disjoint N j
  disjoint N m
  disjoint N n
  disjoint N y
  disjoint T j
  disjoint T m
  disjoint T n
  disjoint T y
  disjoint U j
  disjoint U m
  disjoint U n
  disjoint U y
  disjoint V j
  disjoint V m
  disjoint V n
  disjoint V y
  disjoint i ph
  disjoint k ph
  disjoint p ph
  disjoint ph s
  disjoint ph t
  disjoint B f
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B n
  disjoint B s
  disjoint B t
  disjoint K f
  disjoint K i
  disjoint K j
  disjoint K k
  disjoint K n
  disjoint K p
  disjoint K s
  disjoint K t
  disjoint M f
  disjoint M i
  disjoint M k
  disjoint M p
  disjoint M s
  disjoint M t
  disjoint N f
  disjoint N i
  disjoint N k
  disjoint N p
  disjoint N s
  disjoint N t
  disjoint T f
  disjoint T i
  disjoint T p
  disjoint U f
  disjoint U i
  disjoint U p
  disjoint ph z
  disjoint F f
  disjoint F k
  disjoint F p
  disjoint F s
  disjoint F t
  disjoint F z
  disjoint K z
  disjoint N z
  disjoint T k
  disjoint T s
  disjoint T t
  disjoint T z
  disjoint U k
  disjoint U t
  disjoint ph q
  disjoint ph u
  disjoint ph w
  disjoint ph x
  disjoint B m
  disjoint B q
  disjoint B u
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C i
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C p
  disjoint C q
  disjoint C t
  disjoint C u
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint K m
  disjoint K q
  disjoint K u
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint N q
  disjoint N u
  disjoint N w
  disjoint N x
  disjoint T x
  disjoint U s
  disjoint U x
  disjoint U z
  disjoint V i
  disjoint V k
  disjoint V p
  disjoint V s
  disjoint V x
  disjoint c g
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint c s
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g p
  disjoint g q
  disjoint g r
  disjoint g s
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint g ph
  disjoint i r
  disjoint i v
  disjoint j r
  disjoint j v
  disjoint k r
  disjoint k v
  disjoint m r
  disjoint m v
  disjoint n r
  disjoint n v
  disjoint p r
  disjoint p v
  disjoint q r
  disjoint q v
  disjoint r s
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint ph r
  disjoint s v
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ph v
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a g
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a p
  disjoint a q
  disjoint a r
  disjoint a s
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b p
  disjoint b q
  disjoint b r
  disjoint b s
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint F b
  disjoint c f
  disjoint f g
  disjoint f r
  disjoint f v
  disjoint F g
  disjoint F i
  disjoint F q
  disjoint F r
  disjoint F v
  disjoint F x
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G f
  disjoint G g
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G p
  disjoint G q
  disjoint G r
  disjoint G s
  disjoint G v
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint I a
  disjoint I b
  disjoint I f
  disjoint I g
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint I m
  disjoint I n
  disjoint I p
  disjoint I q
  disjoint I r
  disjoint I s
  disjoint I v
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint N a
  disjoint N b
  disjoint N g
  disjoint N r
  disjoint N v
  disjoint R a
  disjoint R b
  disjoint R f
  disjoint R g
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R m
  disjoint R n
  disjoint R p
  disjoint R q
  disjoint R r
  disjoint R s
  disjoint R v
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint X c
  disjoint X f
  disjoint X g
  disjoint X i
  disjoint X m
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> E. c e. I c = ( F ` c ) )

  proof
    wph
    vc
    cv
    #
    vx
    cI
    vx
    cv
    #
    @1
    cF
    cfv
    #
    cmin
    cof
    #
    co
    #
    cmpt
    #
    cfv
    #
    c1
    cN
    cfz
    co
    #
    cc0
    csn
    cxp
    #
    wceq
    #
    vc
    cI
    wrex
    @0
    @0
    cF
    cfv
    #
    wceq
    #
    vc
    cI
    wrex
    wph
    vz
    cR
    vn
    @5
    cI
    cN
    vc
    poimir.0
    poimir.i
    poimir.r
    wph
    @5
    vx
    cI
    vn
    @7
    vn
    cv
    #
    @1
    cfv
    #
    @12
    @2
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cmpt
    cR
    cI
    crest
    co
    #
    cR
    ccn
    co
    wph
    vx
    cI
    @4
    @16
    wph
    @1
    cI
    wcel
    #
    wa
    #
    vn
    @7
    @7
    @13
    @14
    cmin
    @7
    @1
    @2
    cvv
    cvv
    @18
    @1
    @7
    wfn
    #
    wph
    @20
    @1
    cc0
    c1
    cicc
    co
    #
    @7
    cmap
    co
    #
    cI
    @1
    @21
    @7
    elmapfn
    poimir.i
    eleq2s
    adantl
    @19
    @2
    cI
    wcel
    #
    @2
    @7
    wfn
    #
    wph
    cI
    cI
    @1
    cF
    wph
    cF
    @17
    @17
    ccn
    co
    #
    wcel
    cI
    cI
    cF
    wf
    broucube.1
    cF
    @17
    @17
    cI
    cI
    cI
    @17
    cR
    cr
    @7
    cmap
    co
    #
    ctopon
    cfv
    wcel
    #
    cI
    @26
    wss
    #
    @17
    cI
    ctopon
    cfv
    wcel
    #
    @7
    cvv
    wcel
    #
    cioo
    crn
    #
    ctg
    cfv
    #
    cr
    ctopon
    cfv
    wcel
    @27
    c1
    cN
    cfz
    ovex
    #
    retopon
    @7
    @32
    cR
    cvv
    cr
    poimir.r
    pttoponconst
    mp2an
    #
    cI
    @22
    @26
    poimir.i
    cr
    cvv
    wcel
    @21
    cr
    wss
    @22
    @26
    wss
    reex
    unitssre
    @21
    cr
    @7
    cvv
    mapss
    mp2an
    eqsstri
    #
    cI
    cR
    @26
    resttopon
    mp2an
    #
    toponunii
    #
    @37
    cnf
    syl
    #
    ffvelrnda
    #
    @24
    @2
    @22
    cI
    @2
    @21
    @7
    elmapfn
    poimir.i
    eleq2s
    syl
    @19
    c1
    cN
    cfz
    ovexd
    #
    @40
    @7
    inidm
    #
    @19
    @12
    @7
    wcel
    #
    wa
    #
    @13
    eqidd
    @43
    @14
    eqidd
    offval
    mpteq2dva
    wph
    vx
    @15
    vn
    @7
    @32
    csn
    cxp
    #
    @7
    @17
    cR
    cvv
    cI
    poimir.r
    @29
    wph
    @36
    a1i
    wph
    c1
    cN
    cfz
    ovexd
    @7
    ctop
    @44
    wf
    #
    wph
    @7
    @32
    ctop
    retop
    fconst6
    #
    a1i
    wph
    @42
    wa
    #
    vx
    cI
    @15
    cmpt
    #
    @17
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
    @17
    @12
    @44
    cfv
    #
    ccn
    co
    #
    @47
    @48
    @17
    @49
    ccn
    co
    #
    wcel
    #
    @48
    @51
    wcel
    #
    @47
    vx
    @13
    @14
    cmin
    @17
    @49
    @49
    @49
    cI
    @29
    @47
    @36
    a1i
    #
    @42
    vx
    cI
    @13
    cmpt
    #
    @54
    wcel
    wph
    @42
    @51
    @54
    @58
    @49
    ctop
    wcel
    @51
    @54
    wss
    @49
    @49
    eqid
    #
    cnfldtop
    cr
    @17
    @49
    cnrest2r
    ax-mp
    @42
    @58
    @53
    @51
    @42
    @58
    vx
    @26
    @13
    cmpt
    #
    cI
    cres
    #
    @53
    @28
    @61
    @58
    wceq
    @35
    vx
    @26
    cI
    @13
    resmpt
    ax-mp
    @42
    @60
    cR
    @52
    ccn
    co
    wcel
    #
    @28
    @61
    @53
    wcel
    @30
    @45
    @42
    @62
    @33
    @46
    vx
    @7
    @44
    @12
    cR
    cvv
    @26
    @26
    cR
    @34
    toponunii
    #
    poimir.r
    ptpjcn
    mp3an12
    @35
    cI
    @60
    cR
    @52
    @26
    @63
    cnrest
    sylancl
    syl5eqelr
    @42
    @52
    @50
    @17
    ccn
    @42
    @52
    @32
    @50
    @7
    @32
    @12
    @31
    ctg
    fvex
    fvconst2
    @49
    @59
    tgioo2
    syl6eq
    oveq2d
    #
    eleqtrd
    sseldi
    adantl
    #
    @47
    vx
    vz
    @2
    @12
    vz
    cv
    #
    cfv
    #
    @14
    @17
    @17
    @49
    cI
    cI
    @57
    wph
    vx
    cI
    @2
    cmpt
    #
    @25
    wcel
    @42
    wph
    cF
    @68
    @25
    wph
    vx
    cI
    cI
    cF
    @38
    feqmptd
    broucube.1
    eqeltrrd
    adantr
    @57
    @47
    vz
    cI
    @67
    cmpt
    @58
    @54
    vx
    vz
    cI
    @13
    @67
    @12
    @1
    @66
    fveq1
    cbvmptv
    @65
    syl5eqelr
    @12
    @66
    @2
    fveq1
    cnmpt11
    cmin
    @49
    @49
    ctx
    co
    @49
    ccn
    co
    wcel
    @47
    @49
    @59
    subcn
    a1i
    cnmpt12f
    @47
    cI
    cr
    @48
    wf
    @48
    crn
    cr
    wss
    #
    @55
    @56
    wb
    #
    @47
    vx
    cI
    @15
    cr
    @48
    wph
    @18
    @42
    @15
    cr
    wcel
    @43
    @13
    @14
    @18
    @42
    @13
    cr
    wcel
    wph
    @18
    @42
    wa
    @21
    cr
    @13
    unitssre
    @18
    @7
    @21
    @12
    @1
    @7
    @21
    @1
    wf
    @1
    @22
    cI
    @1
    @21
    @7
    elmapi
    poimir.i
    eleq2s
    ffvelrnda
    sseldi
    adantll
    @43
    @21
    cr
    @14
    unitssre
    @19
    @7
    @21
    @12
    @2
    @19
    @23
    @7
    @21
    @2
    wf
    #
    @39
    @71
    @2
    @22
    cI
    @2
    @21
    @7
    elmapi
    poimir.i
    eleq2s
    syl
    ffvelrnda
    sseldi
    resubcld
    an32s
    @48
    eqid
    fmptd
    cI
    cr
    @48
    frn
    @49
    cc
    ctopon
    cfv
    wcel
    @69
    cr
    cc
    wss
    @70
    @49
    @59
    cnfldtopon
    ax-resscn
    cr
    @48
    @17
    @49
    cc
    cnrest2
    mp3an13
    3syl
    mpbid
    @42
    @53
    @51
    wceq
    wph
    @64
    adantl
    eleqtrrd
    ptcn
    eqeltrd
    wph
    @42
    @66
    cI
    wcel
    #
    @67
    cc0
    wceq
    #
    w3a
    wa
    #
    @12
    @66
    @5
    cfv
    #
    cfv
    #
    @12
    @66
    cF
    cfv
    #
    cfv
    #
    cneg
    #
    cc0
    cle
    @74
    @76
    @12
    @66
    @77
    @3
    co
    #
    cfv
    #
    @79
    @74
    @72
    @76
    @81
    wceq
    #
    wph
    @42
    @72
    @73
    simpr2
    @72
    @12
    @75
    @80
    vx
    @66
    @4
    @80
    cI
    @5
    vx
    vz
    weq
    #
    @1
    @66
    @2
    @77
    @3
    @83
    id
    @1
    @66
    cF
    fveq2
    oveq12d
    @5
    eqid
    #
    @66
    @77
    @3
    ovex
    fvmpt
    fveq1d
    #
    syl
    wph
    @42
    @72
    @73
    @81
    @79
    wceq
    #
    wph
    @73
    @72
    @42
    @86
    wph
    @73
    @72
    @42
    @86
    wph
    @73
    wa
    #
    @72
    wa
    #
    @42
    wa
    #
    @81
    cc0
    @78
    cmin
    co
    @79
    @88
    @7
    @7
    cc0
    @78
    cmin
    @7
    @66
    @77
    cvv
    cvv
    @12
    @72
    @66
    @7
    wfn
    #
    @87
    @90
    @66
    @22
    cI
    @66
    @21
    @7
    elmapfn
    poimir.i
    eleq2s
    #
    adantl
    wph
    @72
    @77
    @7
    wfn
    #
    @73
    wph
    @72
    wa
    #
    @77
    cI
    wcel
    #
    @92
    wph
    cI
    cI
    @66
    cF
    @38
    ffvelrnda
    #
    @92
    @77
    @22
    cI
    @77
    @21
    @7
    elmapfn
    poimir.i
    eleq2s
    syl
    #
    adantlr
    @88
    c1
    cN
    cfz
    ovexd
    #
    @97
    @41
    wph
    @73
    @72
    @42
    simpllr
    @89
    @78
    eqidd
    ofval
    @78
    df-neg
    syl6eqr
    exp41
    com24
    3imp2
    eqtrd
    wph
    @42
    @72
    @79
    cc0
    cle
    wbr
    #
    @73
    wph
    @42
    @72
    @98
    wph
    @72
    @42
    @98
    @93
    @42
    wa
    #
    cc0
    @78
    cle
    wbr
    #
    @98
    @99
    @78
    @21
    wcel
    #
    @100
    @93
    @7
    @21
    @12
    @77
    @93
    @94
    @7
    @21
    @77
    wf
    #
    @95
    @102
    @77
    @22
    cI
    @77
    @21
    @7
    elmapi
    poimir.i
    eleq2s
    syl
    ffvelrnda
    #
    cc0
    cxr
    wcel
    #
    c1
    cxr
    wcel
    #
    @101
    @100
    0xr
    c1
    1re
    rexri
    #
    cc0
    c1
    @78
    iccgelb
    mp3an12
    syl
    @99
    @78
    @99
    @21
    cr
    @78
    unitssre
    @103
    sseldi
    #
    le0neg2d
    mpbid
    an32s
    anasss
    3adantr3
    eqbrtrd
    wph
    @42
    @72
    @67
    c1
    wceq
    #
    w3a
    wa
    #
    cc0
    c1
    @78
    cmin
    co
    #
    @76
    cle
    wph
    @42
    @72
    cc0
    @110
    cle
    wbr
    #
    @108
    wph
    @42
    @72
    @111
    wph
    @72
    @42
    @111
    @99
    @111
    @78
    c1
    cle
    wbr
    #
    @99
    @101
    @112
    @103
    @104
    @105
    @101
    @112
    0xr
    @106
    cc0
    c1
    @78
    iccleub
    mp3an12
    syl
    @99
    c1
    @78
    @99
    1red
    @107
    subge0d
    mpbird
    an32s
    anasss
    3adantr3
    @109
    @76
    @81
    @110
    @109
    @72
    @82
    wph
    @42
    @72
    @108
    simpr2
    @85
    syl
    wph
    @42
    @72
    @108
    @81
    @110
    wceq
    #
    wph
    @108
    @72
    @42
    @113
    wph
    @108
    @72
    @42
    @113
    wph
    @108
    wa
    #
    @72
    wa
    #
    @7
    @7
    c1
    @78
    cmin
    @7
    @66
    @77
    cvv
    cvv
    @12
    @72
    @90
    @114
    @91
    adantl
    wph
    @72
    @92
    @108
    @96
    adantlr
    @115
    c1
    cN
    cfz
    ovexd
    #
    @116
    @41
    wph
    @108
    @72
    @42
    simpllr
    @115
    @42
    wa
    @78
    eqidd
    ofval
    exp41
    com24
    3imp2
    eqtrd
    breqtrrd
    poimir
    wph
    @9
    @11
    vc
    cI
    wph
    @0
    cI
    wcel
    #
    wa
    #
    @9
    @0
    @10
    @3
    co
    #
    @8
    wceq
    #
    @11
    @118
    @6
    @119
    @8
    @117
    @6
    @119
    wceq
    wph
    vx
    @0
    @4
    @119
    cI
    @5
    vx
    vc
    weq
    #
    @1
    @0
    @2
    @10
    @3
    @121
    id
    @1
    @0
    cF
    fveq2
    oveq12d
    @84
    @0
    @10
    @3
    ovex
    fvmpt
    adantl
    eqeq1d
    @118
    @12
    @119
    cfv
    #
    @12
    @8
    cfv
    #
    wceq
    #
    vn
    @7
    wral
    #
    @12
    @0
    cfv
    #
    @12
    @10
    cfv
    #
    wceq
    #
    vn
    @7
    wral
    #
    @120
    @11
    @118
    @124
    @128
    vn
    @7
    @118
    @42
    wa
    #
    @124
    @126
    @127
    cmin
    co
    #
    cc0
    wceq
    @128
    @130
    @122
    @131
    @123
    cc0
    @118
    @7
    @7
    @126
    @127
    cmin
    @7
    @0
    @10
    cvv
    cvv
    @12
    @117
    @0
    @7
    wfn
    #
    wph
    @132
    @0
    @22
    cI
    @0
    @21
    @7
    elmapfn
    poimir.i
    eleq2s
    adantl
    #
    @118
    @10
    cI
    wcel
    #
    @10
    @7
    wfn
    #
    wph
    cI
    cI
    @0
    cF
    @38
    ffvelrnda
    #
    @135
    @10
    @22
    cI
    @10
    @21
    @7
    elmapfn
    poimir.i
    eleq2s
    syl
    #
    @118
    c1
    cN
    cfz
    ovexd
    #
    @138
    @41
    @130
    @126
    eqidd
    @130
    @127
    eqidd
    ofval
    @42
    @123
    cc0
    wceq
    @118
    @7
    cc0
    @12
    c0ex
    fvconst2
    adantl
    eqeq12d
    @130
    @126
    @127
    @117
    @42
    @126
    cc
    wcel
    wph
    @117
    @42
    wa
    @21
    cc
    @126
    @21
    cr
    cc
    unitssre
    ax-resscn
    sstri
    #
    @117
    @7
    @21
    @12
    @0
    @7
    @21
    @0
    wf
    @0
    @22
    cI
    @0
    @21
    @7
    elmapi
    poimir.i
    eleq2s
    ffvelrnda
    sseldi
    adantll
    @130
    @21
    cc
    @127
    @139
    @118
    @7
    @21
    @12
    @10
    @118
    @134
    @7
    @21
    @10
    wf
    #
    @136
    @140
    @10
    @22
    cI
    @10
    @21
    @7
    elmapi
    poimir.i
    eleq2s
    syl
    ffvelrnda
    sseldi
    subeq0ad
    bitrd
    ralbidva
    @118
    @119
    @7
    wfn
    @8
    @7
    wfn
    #
    @120
    @125
    wb
    @118
    @7
    @7
    cmin
    @7
    @0
    @10
    cvv
    cvv
    @133
    @137
    @138
    @138
    @41
    offn
    cc0
    cvv
    wcel
    @141
    c0ex
    @7
    cc0
    cvv
    fnconstg
    ax-mp
    vn
    @7
    @119
    @8
    eqfnfv
    sylancl
    @118
    @132
    @135
    @11
    @129
    wb
    @133
    @137
    vn
    @7
    @0
    @10
    eqfnfv
    syl2anc
    3bitr4d
    bitrd
    rexbidva
    mpbid
end
