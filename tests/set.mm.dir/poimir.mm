include "wel.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "wrex.mm"
include "cle.mm"
include "ccnv.mm"
include "cpr.mm"
include "wral.mm"
include "wi.mm"
include "crest.mm"
include "co.mm"
include "c1.mm"
include "cfz.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "poimirlem32.mm"
include "wcel.mm"
include "wa.mm"
include "wfn.mm"
include "wne.mm"
include "wn.mm"
include "wo.mm"
include "cmpt.mm"
include "cima.mm"
include "cabs.mm"
include "cmin.mm"
include "caddc.mm"
include "cioo.mm"
include "wss.mm"
include "cr.mm"
include "cmap.mm"
include "wf.mm"
include "ccn.mm"
include "ctop.mm"
include "cuni.mm"
include "cvv.mm"
include "crn.mm"
include "ctg.mm"
include "ctopon.mm"
include "ovex.mm"
include "retopon.mm"
include "pttoponconst.mm"
include "mp2an.mm"
include "topontopi.mm"
include "cicc.mm"
include "reex.mm"
include "unitssre.mm"
include "mapss.mm"
include "eqsstri.mm"
include "toponunii.mm"
include "restuni.mm"
include "cnf.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "clt.mm"
include "crp.mm"
include "cc.mm"
include "recn.mm"
include "absrpcl.mm"
include "ex.mm"
include "ltsubrp.mm"
include "ltaddrp.mm"
include "jca.mm"
include "syld.mm"
include "cxr.mm"
include "wb.mm"
include "abscld.mm"
include "resubcl.mm"
include "mpdan.mm"
include "rexrd.mm"
include "readdcl.mm"
include "rexr.mm"
include "elioo5.mm"
include "syl3anc.mm"
include "sylibrd.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eleq1d.mm"
include "ad2antlr.mm"
include "iooretop.mm"
include "ccnp.mm"
include "resttopon.mm"
include "a1i.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "adantr.mm"
include "retop.mm"
include "fconst6.mm"
include "ptpjcn.mm"
include "mp3an12.mm"
include "fvconst2.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "adantl.mm"
include "fveq1.mm"
include "cnmpt11.mm"
include "cncnpi.mm"
include "sylan.mm"
include "an32s.mm"
include "iscnp.mm"
include "mpbid.mm"
include "simprd.mm"
include "eleq2.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpsyl.mm"
include "0re.mm"
include "letric.mm"
include "sylancl.mm"
include "jctird.mm"
include "r19.41v.mm"
include "anass.mm"
include "rexbii.mm"
include "bitr3i.mm"
include "syl6ib.mm"
include "eltopss.mm"
include "mpan.mm"
include "cdm.mm"
include "dmmpti.mm"
include "sseq2i.mm"
include "wfun.mm"
include "funmpt.mm"
include "funimass4.mm"
include "sylbir.mm"
include "ssel2.mm"
include "eliooord.mm"
include "syl6bi.mm"
include "ralimdva.mm"
include "sylbid.mm"
include "cneg.mm"
include "absnid.mm"
include "negidd.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "0red.mm"
include "ltnled.mm"
include "adantllr.mm"
include "adantlr.mm"
include "bitrd.mm"
include "biimpd.mm"
include "sylan2.mm"
include "anassrs.mm"
include "adantld.mm"
include "impancom.mm"
include "absid.mm"
include "subidd.mm"
include "breq1d.mm"
include "adantrd.mm"
include "orim12d.mm"
include "expimpd.mm"
include "syland.mm"
include "anim2d.mm"
include "reximdva.mm"
include "ralnex.mm"
include "ctsr.mm"
include "letsr.mm"
include "elexi.mm"
include "cnvex.mm"
include "breq.mm"
include "notbid.mm"
include "ralbidv.mm"
include "c0ex.mm"
include "brcnv.mm"
include "syl6bb.mm"
include "rexpr.mm"
include "rexnal.mm"
include "3bitr3i.mm"
include "anbi2i.mm"
include "annim.mm"
include "bitri.mm"
include "necon4ad.mm"
include "ffn.mm"
include "jctild.mm"
include "fconstfv.mm"
include "fconst2.mm"
include "mpd.mm"

theorem poimir
  let wph: wff ph
  let vz: setvar z
  let cR: class R
  let vn: setvar n
  let cF: class F
  let cI: class I
  let cN: class N
  let vc: setvar c
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
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
  assume poimir.1: |- ( ph -> F e. ( ( R |`t I ) Cn R ) )
  assume poimir.2: |- ( ( ph /\ ( n e. ( 1 ... N ) /\ z e. I /\ ( z ` n ) = 0 ) ) -> ( ( F ` z ) ` n ) <_ 0 )
  assume poimir.3: |- ( ( ph /\ ( n e. ( 1 ... N ) /\ z e. I /\ ( z ` n ) = 1 ) ) -> 0 <_ ( ( F ` z ) ` n ) )

  disjoint n z
  disjoint n ph
  disjoint F n
  disjoint N n
  disjoint ph z
  disjoint F z
  disjoint N z
  disjoint c n
  disjoint c z
  disjoint c ph
  disjoint F c
  disjoint I c
  disjoint I n
  disjoint I z
  disjoint N c
  disjoint R c
  disjoint R n
  disjoint R z
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
  disjoint ph y
  disjoint F j
  disjoint F m
  disjoint F y
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M y
  disjoint N j
  disjoint N m
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
  disjoint F f
  disjoint F k
  disjoint F p
  disjoint F s
  disjoint F t
  disjoint K z
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
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint c s
  disjoint c v
  disjoint c x
  disjoint c y
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
  disjoint I p
  disjoint I q
  disjoint I r
  disjoint I s
  disjoint I v
  disjoint I x
  disjoint I y
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
  disjoint R p
  disjoint R q
  disjoint R r
  disjoint R s
  disjoint R v
  disjoint R x
  disjoint R y
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
  assert |- ( ph -> E. c e. I ( F ` c ) = ( ( 1 ... N ) X. { 0 } ) )

  proof
    wph
    vc
    vv
    wel
    #
    cc0
    vn
    cv
    #
    vz
    cv
    #
    cF
    cfv
    #
    cfv
    #
    vr
    cv
    #
    wbr
    #
    vz
    vv
    cv
    #
    wrex
    #
    vr
    cle
    cle
    ccnv
    #
    cpr
    #
    wral
    #
    wi
    #
    vv
    cR
    cI
    crest
    co
    #
    wral
    #
    vn
    c1
    cN
    cfz
    co
    #
    wral
    #
    vc
    cI
    wrex
    vc
    cv
    #
    cF
    cfv
    #
    @15
    cc0
    csn
    #
    cxp
    wceq
    #
    vc
    cI
    wrex
    wph
    vz
    vv
    cR
    vn
    cF
    cI
    cN
    vr
    vc
    poimir.0
    poimir.i
    poimir.r
    poimir.1
    poimir.2
    poimir.3
    poimirlem32
    wph
    @16
    @20
    vc
    cI
    wph
    @17
    cI
    wcel
    #
    wa
    #
    @16
    @18
    @15
    wfn
    #
    @1
    @18
    cfv
    #
    cc0
    wceq
    #
    vn
    @15
    wral
    #
    wa
    #
    @20
    @22
    @16
    @26
    @23
    @22
    @14
    @25
    vn
    @15
    @22
    @1
    @15
    wcel
    #
    wa
    #
    @14
    @24
    cc0
    @29
    @24
    cc0
    wne
    #
    @0
    cc0
    @4
    cle
    wbr
    #
    wn
    #
    vz
    @7
    wral
    #
    @4
    cc0
    cle
    wbr
    #
    wn
    #
    vz
    @7
    wral
    #
    wo
    #
    wa
    #
    vv
    @13
    wrex
    #
    @14
    wn
    #
    @29
    @30
    @0
    vx
    cI
    @1
    vx
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    @7
    cima
    #
    @24
    @24
    cabs
    cfv
    #
    cmin
    co
    #
    @24
    @46
    caddc
    co
    #
    cioo
    co
    #
    wss
    #
    @24
    cc0
    cle
    wbr
    #
    cc0
    @24
    cle
    wbr
    #
    wo
    #
    wa
    #
    wa
    #
    vv
    @13
    wrex
    #
    @39
    @29
    @30
    @0
    @50
    wa
    #
    vv
    @13
    wrex
    #
    @53
    wa
    #
    @56
    @29
    @30
    @58
    @53
    @29
    @30
    @17
    @44
    cfv
    #
    @49
    wcel
    #
    @58
    @29
    @30
    @24
    @49
    wcel
    #
    @61
    @29
    @24
    cr
    wcel
    #
    @30
    @62
    wi
    @22
    @15
    cr
    @1
    @18
    @22
    @18
    cr
    @15
    cmap
    co
    #
    wcel
    @15
    cr
    @18
    wf
    #
    wph
    cI
    @64
    @17
    cF
    wph
    cF
    @13
    cR
    ccn
    co
    #
    wcel
    cI
    @64
    cF
    wf
    poimir.1
    cF
    @13
    cR
    cI
    @64
    cR
    ctop
    wcel
    cI
    @64
    wss
    #
    cI
    @13
    cuni
    wceq
    @64
    cR
    @15
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
    #
    cR
    @64
    ctopon
    cfv
    wcel
    #
    c1
    cN
    cfz
    ovex
    #
    retopon
    @15
    @70
    cR
    cvv
    cr
    poimir.r
    pttoponconst
    mp2an
    #
    topontopi
    cI
    cc0
    c1
    cicc
    co
    #
    @15
    cmap
    co
    #
    @64
    poimir.i
    cr
    cvv
    wcel
    @75
    cr
    wss
    @76
    @64
    wss
    reex
    unitssre
    @75
    cr
    @15
    cvv
    mapss
    mp2an
    eqsstri
    #
    cI
    cR
    @64
    @64
    cR
    @74
    toponunii
    #
    restuni
    mp2an
    #
    @78
    cnf
    syl
    #
    ffvelrnda
    @18
    cr
    @15
    elmapi
    syl
    #
    ffvelrnda
    #
    @63
    @30
    @47
    @24
    clt
    wbr
    #
    @24
    @48
    clt
    wbr
    #
    wa
    #
    @62
    @63
    @30
    @46
    crp
    wcel
    #
    @85
    @63
    @24
    cc
    wcel
    #
    @30
    @86
    wi
    @24
    recn
    #
    @87
    @30
    @86
    @24
    absrpcl
    ex
    syl
    @63
    @86
    @85
    @63
    @86
    wa
    @83
    @84
    @24
    @46
    ltsubrp
    @24
    @46
    ltaddrp
    jca
    ex
    syld
    @63
    @47
    cxr
    wcel
    @48
    cxr
    wcel
    @24
    cxr
    wcel
    @62
    @85
    wb
    @63
    @47
    @63
    @46
    cr
    wcel
    #
    @47
    cr
    wcel
    @63
    @24
    @88
    abscld
    #
    @24
    @46
    resubcl
    mpdan
    rexrd
    @63
    @48
    @63
    @89
    @48
    cr
    wcel
    @90
    @24
    @46
    readdcl
    mpdan
    rexrd
    @24
    rexr
    @47
    @48
    @24
    elioo5
    syl3anc
    sylibrd
    syl
    @21
    @61
    @62
    wb
    wph
    @28
    @21
    @60
    @24
    @49
    vx
    @17
    @43
    @24
    cI
    @44
    vx
    vc
    weq
    @1
    @42
    @18
    @41
    @17
    cF
    fveq2
    fveq1d
    @44
    eqid
    #
    @1
    @18
    fvex
    fvmpt
    eleq1d
    ad2antlr
    sylibrd
    @49
    @70
    wcel
    @29
    @60
    @2
    wcel
    #
    @0
    @45
    @2
    wss
    #
    wa
    #
    vv
    @13
    wrex
    #
    wi
    #
    vz
    @70
    wral
    #
    @61
    @58
    wi
    #
    @47
    @48
    iooretop
    @29
    cI
    cr
    @44
    wf
    #
    @97
    @29
    @44
    @17
    @13
    @70
    ccnp
    co
    cfv
    wcel
    #
    @99
    @97
    wa
    #
    wph
    @28
    @21
    @100
    wph
    @28
    wa
    #
    @44
    @13
    @70
    ccn
    co
    wcel
    @21
    @100
    @102
    vx
    vz
    @42
    @1
    @2
    cfv
    #
    @43
    @13
    cR
    @70
    cI
    @64
    @13
    cI
    ctopon
    cfv
    wcel
    #
    @102
    @72
    @67
    @104
    @74
    @77
    cI
    cR
    @64
    resttopon
    mp2an
    #
    a1i
    wph
    vx
    cI
    @42
    cmpt
    #
    @66
    wcel
    @28
    wph
    cF
    @106
    @66
    wph
    vx
    cI
    @64
    cF
    @80
    feqmptd
    poimir.1
    eqeltrrd
    adantr
    @72
    @102
    @74
    a1i
    @28
    vz
    @64
    @103
    cmpt
    #
    cR
    @70
    ccn
    co
    #
    wcel
    wph
    @28
    @107
    cR
    @1
    @15
    @70
    csn
    cxp
    #
    cfv
    #
    ccn
    co
    #
    @108
    @68
    @15
    ctop
    @109
    wf
    @28
    @107
    @111
    wcel
    @73
    @15
    @70
    ctop
    retop
    fconst6
    vz
    @15
    @109
    @1
    cR
    cvv
    @64
    @78
    poimir.r
    ptpjcn
    mp3an12
    @28
    @110
    @70
    cR
    ccn
    @15
    @70
    @1
    @69
    ctg
    fvex
    fvconst2
    oveq2d
    eleqtrd
    adantl
    @1
    @2
    @42
    fveq1
    cnmpt11
    @17
    @44
    @13
    @70
    cI
    @79
    cncnpi
    sylan
    an32s
    @21
    @100
    @101
    wb
    #
    wph
    @28
    @104
    @71
    @21
    @112
    @105
    retopon
    vv
    vz
    @17
    @44
    @13
    @70
    cI
    cr
    iscnp
    mp3an12
    ad2antlr
    mpbid
    simprd
    @96
    @98
    vz
    @49
    @70
    @2
    @49
    wceq
    #
    @92
    @61
    @95
    @58
    @2
    @49
    @60
    eleq2
    @113
    @94
    @57
    vv
    @13
    @113
    @93
    @50
    @0
    @2
    @49
    @45
    sseq2
    anbi2d
    rexbidv
    imbi12d
    rspcv
    mpsyl
    syld
    @29
    @63
    cc0
    cr
    wcel
    @53
    @82
    0re
    @24
    cc0
    letric
    sylancl
    jctird
    @59
    @57
    @53
    wa
    #
    vv
    @13
    wrex
    @56
    @57
    @53
    vv
    @13
    r19.41v
    @114
    @55
    vv
    @13
    @0
    @50
    @53
    anass
    rexbii
    bitr3i
    syl6ib
    @29
    @55
    @38
    vv
    @13
    @29
    @7
    @13
    wcel
    #
    wa
    @54
    @37
    @0
    @115
    @29
    @7
    cI
    wss
    #
    @54
    @37
    wi
    @13
    ctop
    wcel
    @115
    @116
    cI
    @13
    @105
    topontopi
    @7
    @13
    cI
    @79
    eltopss
    mpan
    @29
    @116
    wa
    #
    @50
    @47
    @4
    clt
    wbr
    #
    @4
    @48
    clt
    wbr
    #
    wa
    #
    vz
    @7
    wral
    #
    @53
    @37
    @116
    @50
    @121
    wi
    @29
    @116
    @50
    @2
    @44
    cfv
    #
    @49
    wcel
    #
    vz
    @7
    wral
    #
    @121
    @116
    @7
    @44
    cdm
    #
    wss
    #
    @50
    @124
    wb
    #
    @125
    cI
    @7
    vx
    cI
    @43
    @44
    @1
    @42
    fvex
    @91
    dmmpti
    sseq2i
    @44
    wfun
    @126
    @127
    vx
    cI
    @43
    funmpt
    vz
    @7
    @49
    @44
    funimass4
    mpan
    sylbir
    @116
    @123
    @120
    vz
    @7
    @116
    vz
    vv
    wel
    #
    wa
    #
    @2
    cI
    wcel
    #
    @123
    @120
    wi
    @7
    cI
    @2
    ssel2
    #
    @130
    @123
    @4
    @49
    wcel
    @120
    @130
    @122
    @4
    @49
    vx
    @2
    @43
    @4
    cI
    @44
    vx
    vz
    weq
    @1
    @42
    @3
    @41
    @2
    cF
    fveq2
    fveq1d
    @91
    @1
    @3
    fvex
    #
    fvmpt
    eleq1d
    @4
    @47
    @48
    eliooord
    syl6bi
    syl
    ralimdva
    sylbid
    adantl
    @117
    @121
    @53
    @37
    @117
    @121
    wa
    @51
    @33
    @52
    @36
    @117
    @51
    @121
    @33
    @29
    @51
    @116
    @121
    @33
    wi
    @29
    @51
    wa
    #
    @116
    wa
    #
    @120
    @32
    vz
    @7
    @134
    @128
    wa
    @119
    @32
    @118
    @133
    @116
    @128
    @119
    @32
    wi
    #
    @129
    @133
    @130
    @135
    @131
    @133
    @130
    wa
    #
    @119
    @32
    @136
    @119
    @4
    cc0
    clt
    wbr
    #
    @32
    @136
    @48
    cc0
    @4
    clt
    @133
    @48
    cc0
    wceq
    #
    @130
    @29
    @63
    @51
    @138
    @82
    @63
    @51
    wa
    #
    @48
    @24
    @24
    cneg
    #
    caddc
    co
    #
    cc0
    @139
    @46
    @140
    @24
    caddc
    @24
    absnid
    oveq2d
    @63
    @141
    cc0
    wceq
    @51
    @63
    @24
    @88
    negidd
    adantr
    eqtrd
    sylan
    adantr
    breq2d
    @29
    @130
    @137
    @32
    wb
    #
    @51
    wph
    @28
    @130
    @142
    @21
    @102
    @130
    wa
    #
    @4
    cc0
    wph
    @130
    @28
    @4
    cr
    wcel
    wph
    @130
    wa
    #
    @15
    cr
    @1
    @3
    @144
    @3
    @64
    wcel
    @15
    cr
    @3
    wf
    wph
    cI
    @64
    @2
    cF
    @80
    ffvelrnda
    @3
    cr
    @15
    elmapi
    syl
    ffvelrnda
    an32s
    #
    @143
    0red
    #
    ltnled
    adantllr
    adantlr
    bitrd
    biimpd
    sylan2
    anassrs
    adantld
    ralimdva
    an32s
    impancom
    @117
    @52
    @121
    @36
    @29
    @52
    @116
    @121
    @36
    wi
    @29
    @52
    wa
    #
    @116
    wa
    #
    @120
    @35
    vz
    @7
    @148
    @128
    wa
    @118
    @35
    @119
    @147
    @116
    @128
    @118
    @35
    wi
    #
    @129
    @147
    @130
    @149
    @131
    @147
    @130
    wa
    #
    @118
    @35
    @150
    @118
    cc0
    @4
    clt
    wbr
    #
    @35
    @150
    @47
    cc0
    @4
    clt
    @147
    @47
    cc0
    wceq
    #
    @130
    @29
    @63
    @52
    @152
    @82
    @63
    @52
    wa
    #
    @47
    @24
    @24
    cmin
    co
    #
    cc0
    @153
    @46
    @24
    @24
    cmin
    @24
    absid
    oveq2d
    @63
    @154
    cc0
    wceq
    @52
    @63
    @24
    @88
    subidd
    adantr
    eqtrd
    sylan
    adantr
    breq1d
    @29
    @130
    @151
    @35
    wb
    #
    @52
    wph
    @28
    @130
    @155
    @21
    @143
    cc0
    @4
    @146
    @145
    ltnled
    adantllr
    adantlr
    bitrd
    biimpd
    sylan2
    anassrs
    adantrd
    ralimdva
    an32s
    impancom
    orim12d
    expimpd
    syland
    sylan2
    anim2d
    reximdva
    syld
    @39
    @12
    wn
    #
    vv
    @13
    wrex
    @40
    @38
    @156
    vv
    @13
    @38
    @0
    @11
    wn
    #
    wa
    @156
    @37
    @157
    @0
    @6
    wn
    #
    vz
    @7
    wral
    #
    vr
    @10
    wrex
    @8
    wn
    #
    vr
    @10
    wrex
    @37
    @157
    @159
    @160
    vr
    @10
    @6
    vz
    @7
    ralnex
    rexbii
    @159
    @33
    @36
    vr
    cle
    @9
    cle
    ctsr
    letsr
    elexi
    #
    cle
    @161
    cnvex
    @5
    cle
    wceq
    #
    @158
    @32
    vz
    @7
    @162
    @6
    @31
    cc0
    @4
    @5
    cle
    breq
    notbid
    ralbidv
    @5
    @9
    wceq
    #
    @158
    @35
    vz
    @7
    @163
    @6
    @34
    @163
    @6
    cc0
    @4
    @9
    wbr
    @34
    cc0
    @4
    @5
    @9
    breq
    cc0
    @4
    cle
    c0ex
    @132
    brcnv
    syl6bb
    notbid
    ralbidv
    rexpr
    @8
    vr
    @10
    rexnal
    3bitr3i
    anbi2i
    @0
    @11
    annim
    bitri
    rexbii
    @12
    vv
    @13
    rexnal
    bitri
    syl6ib
    necon4ad
    ralimdva
    @22
    @65
    @23
    @81
    @15
    cr
    @18
    ffn
    syl
    jctild
    @27
    @15
    @19
    @18
    wf
    @20
    vn
    @15
    cc0
    @18
    fconstfv
    @15
    cc0
    @18
    c0ex
    fconst2
    bitr3i
    syl6ib
    reximdva
    mpd
end
