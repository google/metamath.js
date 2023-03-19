include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "wcel.mm"
include "creverse.mm"
include "cfv.mm"
include "ccom.mm"
include "cconcat.mm"
include "co.mm"
include "c0.mm"
include "wbr.mm"
include "cid.mm"
include "fviss.mm"
include "eqsstri.mm"
include "sseli.mm"
include "cv.mm"
include "wi.mm"
include "cs1.mm"
include "wceq.mm"
include "id.mm"
include "fveq2.mm"
include "rev0.mm"
include "syl6eq.mm"
include "coeq2d.mm"
include "co02.mm"
include "oveq12d.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "wrd0.mm"
include "ccatlid.mm"
include "ax-mp.mm"
include "wer.mm"
include "efger.mm"
include "a1i.mm"
include "cvv.mm"
include "efgrcl.mm"
include "simprd.mm"
include "syl5eleqr.mm"
include "erref.mm"
include "syl5eqbr.mm"
include "wa.mm"
include "crn.mm"
include "simprl.mm"
include "wf.mm"
include "revcl.mm"
include "ad2antrl.mm"
include "efgmf.mm"
include "wrdco.mm"
include "sylancl.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "chash.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "cc0.mm"
include "cfz.mm"
include "cuz.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "caddc.mm"
include "ccatlen.mm"
include "cz.mm"
include "nn0zd.mm"
include "uzid.mm"
include "syl.mm"
include "uzaddcl.mm"
include "eqeltrd.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "simprr.mm"
include "efgtval.mm"
include "syl3anc.mm"
include "ffvelrni.mm"
include "s2cld.mm"
include "ccatrid.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqidd.mm"
include "hash0.mm"
include "oveq2i.mm"
include "nn0cnd.mm"
include "addid1d.mm"
include "syl5req.mm"
include "splval2.mm"
include "s1cld.mm"
include "revccat.mm"
include "revs1.mm"
include "oveq1i.mm"
include "ccatco.mm"
include "s1co.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "ccatass.mm"
include "df-s2.mm"
include "syl6eqr.mm"
include "3eqtr2rd.mm"
include "wfn.mm"
include "cmpt2.mm"
include "efgtf.mm"
include "ffn.mm"
include "3syl.mm"
include "fnovrn.mm"
include "eqeltrrd.mm"
include "efgi2.mm"
include "ersym.mm"
include "ertr.mm"
include "mpand.mm"
include "expcom.mm"
include "a2d.mm"
include "wrdind.mm"
include "mpcom.mm"

theorem efginvrel2
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let c.sm: class .~
  let cT: class T
  let vn: setvar n
  let cI: class I
  let cM: class M
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let cJ: class J
  let cL: class L
  let cF: class F
  let cK: class K
  let vt: setvar t
  let cP: class P
  let wph: wff ph
  let vm: setvar m
  let vx: setvar x
  let cN: class N
  let cU: class U
  let vk: setvar k
  let vo: setvar o
  let cV: class V
  let cX: class X
  let cQ: class Q
  let cB: class B
  let cC: class C
  let cS: class S
  let cY: class Y
  let cD: class D
  assume efgval.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume efgval.r: |- .~ = ( ~FG ` I )
  assume efgval2.m: |- M = ( y e. I , z e. 2o |-> <. y , ( 1o \ z ) >. )
  assume efgval2.t: |- T = ( v e. W |-> ( n e. ( 0 ... ( # ` v ) ) , w e. ( I X. 2o ) |-> ( v splice <. n , n , <" w ( M ` w ) "> >. ) ) )

  disjoint y z
  disjoint n v
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint w y
  disjoint w z
  disjoint M n
  disjoint M v
  disjoint M w
  disjoint W n
  disjoint W v
  disjoint W w
  disjoint W y
  disjoint W z
  disjoint .~ y
  disjoint .~ z
  disjoint I n
  disjoint I v
  disjoint I w
  disjoint I y
  disjoint I z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a i
  disjoint a j
  disjoint a r
  disjoint a s
  disjoint a u
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b i
  disjoint b j
  disjoint b r
  disjoint b s
  disjoint b u
  disjoint A b
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c i
  disjoint c j
  disjoint c r
  disjoint c s
  disjoint c u
  disjoint A c
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d i
  disjoint d j
  disjoint d r
  disjoint d s
  disjoint d u
  disjoint A d
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint f j
  disjoint f r
  disjoint f s
  disjoint f u
  disjoint A f
  disjoint g h
  disjoint g i
  disjoint g j
  disjoint g r
  disjoint g s
  disjoint g u
  disjoint A g
  disjoint h i
  disjoint h j
  disjoint h r
  disjoint h s
  disjoint h u
  disjoint A h
  disjoint i j
  disjoint i r
  disjoint i s
  disjoint i u
  disjoint A i
  disjoint j r
  disjoint j s
  disjoint j u
  disjoint A j
  disjoint r s
  disjoint r u
  disjoint A r
  disjoint s u
  disjoint A s
  disjoint A u
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b y
  disjoint b z
  disjoint J b
  disjoint r y
  disjoint r z
  disjoint J r
  disjoint J y
  disjoint J z
  disjoint L a
  disjoint L b
  disjoint L f
  disjoint L g
  disjoint L h
  disjoint L r
  disjoint L s
  disjoint L u
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F i
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K r
  disjoint c n
  disjoint c t
  disjoint c v
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint P c
  disjoint n t
  disjoint P n
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint P t
  disjoint P v
  disjoint P w
  disjoint P y
  disjoint P z
  disjoint c ph
  disjoint i ph
  disjoint j ph
  disjoint ph r
  disjoint ph s
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint M a
  disjoint b m
  disjoint b n
  disjoint b t
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint M b
  disjoint c m
  disjoint c x
  disjoint M c
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint M f
  disjoint g m
  disjoint g n
  disjoint g t
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint M g
  disjoint i m
  disjoint i n
  disjoint i t
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint M i
  disjoint j m
  disjoint j n
  disjoint j t
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint M j
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint M m
  disjoint n r
  disjoint n s
  disjoint n u
  disjoint n x
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint M r
  disjoint s t
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint M s
  disjoint t u
  disjoint t x
  disjoint M t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint M u
  disjoint v x
  disjoint w x
  disjoint M x
  disjoint N a
  disjoint N b
  disjoint N i
  disjoint N r
  disjoint U n
  disjoint U v
  disjoint U w
  disjoint U y
  disjoint U z
  disjoint a k
  disjoint a o
  disjoint T a
  disjoint b k
  disjoint b o
  disjoint T b
  disjoint c k
  disjoint c o
  disjoint T c
  disjoint f k
  disjoint f o
  disjoint T f
  disjoint g k
  disjoint g o
  disjoint T g
  disjoint i k
  disjoint i o
  disjoint T i
  disjoint j k
  disjoint j o
  disjoint T j
  disjoint k m
  disjoint k o
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k x
  disjoint T k
  disjoint m o
  disjoint T m
  disjoint o r
  disjoint o s
  disjoint o t
  disjoint o u
  disjoint o x
  disjoint T o
  disjoint T r
  disjoint T s
  disjoint T t
  disjoint T u
  disjoint T x
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint X a
  disjoint X b
  disjoint X i
  disjoint X j
  disjoint X u
  disjoint Q c
  disjoint Q n
  disjoint Q t
  disjoint Q v
  disjoint Q w
  disjoint Q y
  disjoint Q z
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d o
  disjoint d t
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint W d
  disjoint f y
  disjoint f z
  disjoint W f
  disjoint g y
  disjoint g z
  disjoint W g
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h o
  disjoint h t
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint W h
  disjoint i y
  disjoint i z
  disjoint W i
  disjoint j y
  disjoint j z
  disjoint W j
  disjoint k n
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint W k
  disjoint m y
  disjoint m z
  disjoint W m
  disjoint n o
  disjoint o v
  disjoint o w
  disjoint o y
  disjoint o z
  disjoint W o
  disjoint W r
  disjoint s y
  disjoint s z
  disjoint W s
  disjoint W t
  disjoint u y
  disjoint u z
  disjoint W u
  disjoint x y
  disjoint x z
  disjoint W x
  disjoint .~ a
  disjoint .~ b
  disjoint .~ c
  disjoint .~ d
  disjoint .~ f
  disjoint .~ g
  disjoint .~ i
  disjoint .~ j
  disjoint .~ m
  disjoint .~ r
  disjoint .~ s
  disjoint .~ t
  disjoint .~ u
  disjoint .~ x
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B i
  disjoint B j
  disjoint B r
  disjoint B s
  disjoint B u
  disjoint C a
  disjoint C b
  disjoint C i
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C t
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S i
  disjoint S j
  disjoint S o
  disjoint S r
  disjoint S s
  disjoint S u
  disjoint Y i
  disjoint Y j
  disjoint I a
  disjoint I b
  disjoint I c
  disjoint I f
  disjoint I g
  disjoint I i
  disjoint I j
  disjoint I m
  disjoint I r
  disjoint I s
  disjoint I t
  disjoint I u
  disjoint I x
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D m
  disjoint D r
  disjoint D s
  disjoint D t
  disjoint D u
  assert |- ( A e. W -> ( A ++ ( M o. ( reverse ` A ) ) ) .~ (/) )

  proof
    cA
    cI
    c2o
    cxp
    #
    cword
    #
    wcel
    cA
    cW
    wcel
    #
    cA
    cM
    cA
    creverse
    cfv
    #
    ccom
    #
    cconcat
    co
    #
    c0
    c.sm
    wbr
    #
    cW
    @1
    cA
    cW
    @1
    cid
    cfv
    @1
    efgval.w
    @1
    fviss
    eqsstri
    sseli
    @2
    vc
    cv
    #
    cM
    @7
    creverse
    cfv
    #
    ccom
    #
    cconcat
    co
    #
    c0
    c.sm
    wbr
    #
    wi
    @2
    c0
    c0
    cconcat
    co
    #
    c0
    c.sm
    wbr
    #
    wi
    @2
    va
    cv
    #
    cM
    @14
    creverse
    cfv
    #
    ccom
    #
    cconcat
    co
    #
    c0
    c.sm
    wbr
    #
    wi
    @2
    @14
    vb
    cv
    #
    cs1
    #
    cconcat
    co
    #
    cM
    @21
    creverse
    cfv
    #
    ccom
    #
    cconcat
    co
    #
    c0
    c.sm
    wbr
    #
    wi
    @2
    @6
    wi
    vc
    va
    vb
    cA
    @0
    @7
    c0
    wceq
    #
    @11
    @13
    @2
    @26
    @10
    @12
    c0
    c.sm
    @26
    @7
    c0
    @9
    c0
    cconcat
    @26
    id
    @26
    @9
    cM
    c0
    ccom
    c0
    @26
    @8
    c0
    cM
    @26
    @8
    c0
    creverse
    cfv
    c0
    @7
    c0
    creverse
    fveq2
    rev0
    syl6eq
    coeq2d
    cM
    co02
    syl6eq
    oveq12d
    breq1d
    imbi2d
    @7
    @14
    wceq
    #
    @11
    @18
    @2
    @27
    @10
    @17
    c0
    c.sm
    @27
    @7
    @14
    @9
    @16
    cconcat
    @27
    id
    @27
    @8
    @15
    cM
    @7
    @14
    creverse
    fveq2
    coeq2d
    oveq12d
    breq1d
    imbi2d
    @7
    @21
    wceq
    #
    @11
    @25
    @2
    @28
    @10
    @24
    c0
    c.sm
    @28
    @7
    @21
    @9
    @23
    cconcat
    @28
    id
    @28
    @8
    @22
    cM
    @7
    @21
    creverse
    fveq2
    coeq2d
    oveq12d
    breq1d
    imbi2d
    @7
    cA
    wceq
    #
    @11
    @6
    @2
    @29
    @10
    @5
    c0
    c.sm
    @29
    @7
    cA
    @9
    @4
    cconcat
    @29
    id
    @29
    @8
    @3
    cM
    @7
    cA
    creverse
    fveq2
    coeq2d
    oveq12d
    breq1d
    imbi2d
    @2
    @12
    c0
    c0
    c.sm
    c0
    @1
    wcel
    #
    @12
    c0
    wceq
    @0
    wrd0
    #
    @0
    c0
    ccatlid
    ax-mp
    @2
    c0
    c.sm
    cW
    cW
    c.sm
    wer
    #
    @2
    c.sm
    cI
    cW
    efgval.w
    efgval.r
    efger
    #
    a1i
    @2
    c0
    @1
    cW
    @31
    @2
    cI
    cvv
    wcel
    cW
    @1
    wceq
    #
    cA
    cI
    cW
    efgval.w
    efgrcl
    simprd
    #
    syl5eleqr
    erref
    syl5eqbr
    @14
    @1
    wcel
    #
    @19
    @0
    wcel
    #
    wa
    #
    @2
    @18
    @25
    @2
    @38
    @18
    @25
    wi
    @2
    @38
    wa
    #
    @24
    @17
    c.sm
    wbr
    @18
    @25
    @39
    @17
    @24
    c.sm
    cW
    @32
    @39
    @33
    a1i
    #
    @39
    @17
    cW
    wcel
    #
    @24
    @17
    cT
    cfv
    #
    crn
    #
    wcel
    @17
    @24
    c.sm
    wbr
    @39
    @17
    @1
    cW
    @39
    @36
    @16
    @1
    wcel
    #
    @17
    @1
    wcel
    @2
    @36
    @37
    simprl
    #
    @39
    @15
    @1
    wcel
    #
    @0
    @0
    cM
    wf
    #
    @44
    @36
    @46
    @2
    @37
    @0
    @14
    revcl
    ad2antrl
    #
    vy
    vz
    cI
    cM
    efgval2.m
    efgmf
    #
    @0
    @0
    cM
    @15
    wrdco
    sylancl
    #
    @0
    @14
    @16
    ccatcl
    syl2anc
    @2
    @34
    @38
    @35
    adantr
    eleqtrrd
    #
    @39
    @14
    chash
    cfv
    #
    @19
    @42
    co
    #
    @24
    @43
    @39
    @53
    @17
    @52
    @52
    @19
    @19
    cM
    cfv
    #
    cs2
    #
    cotp
    csplice
    co
    #
    @14
    @55
    cconcat
    co
    #
    @16
    cconcat
    co
    #
    @24
    @39
    @41
    @52
    cc0
    @17
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    @37
    @53
    @56
    wceq
    @51
    @39
    @52
    cc0
    cuz
    cfv
    #
    wcel
    @59
    @52
    cuz
    cfv
    #
    wcel
    @61
    @39
    @52
    cn0
    @62
    @36
    @52
    cn0
    wcel
    @2
    @37
    @0
    @14
    lencl
    ad2antrl
    #
    nn0uz
    syl6eleq
    @39
    @59
    @52
    @16
    chash
    cfv
    #
    caddc
    co
    #
    @63
    @39
    @36
    @44
    @59
    @66
    wceq
    @45
    @50
    @0
    @14
    @16
    ccatlen
    syl2anc
    @39
    @52
    @63
    wcel
    #
    @65
    cn0
    wcel
    #
    @66
    @63
    wcel
    @39
    @52
    cz
    wcel
    @67
    @39
    @52
    @64
    nn0zd
    @52
    uzid
    syl
    @39
    @44
    @68
    @50
    @0
    @16
    lencl
    syl
    @65
    @52
    @52
    uzaddcl
    syl2anc
    eqeltrd
    @52
    cc0
    @59
    elfzuzb
    sylanbrc
    #
    @2
    @36
    @37
    simprr
    #
    vy
    vz
    vw
    vv
    @19
    c.sm
    cT
    vn
    cI
    cM
    @52
    cW
    @17
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtval
    syl3anc
    @39
    @14
    c0
    @16
    @55
    @17
    @52
    @52
    @0
    @45
    @30
    @39
    @31
    a1i
    @50
    @39
    @19
    @54
    @0
    @70
    @39
    @37
    @54
    @0
    wcel
    @70
    @0
    @0
    @19
    cM
    @49
    ffvelrni
    syl
    #
    s2cld
    @39
    @14
    @14
    c0
    cconcat
    co
    #
    @16
    cconcat
    @39
    @72
    @14
    @36
    @72
    @14
    wceq
    @2
    @37
    @0
    @14
    ccatrid
    ad2antrl
    eqcomd
    oveq1d
    @39
    @52
    eqidd
    @39
    @52
    c0
    chash
    cfv
    #
    caddc
    co
    @52
    cc0
    caddc
    co
    @52
    @73
    cc0
    @52
    caddc
    hash0
    oveq2i
    @39
    @52
    @39
    @52
    @64
    nn0cnd
    addid1d
    syl5req
    splval2
    @39
    @24
    @21
    @54
    cs1
    #
    @16
    cconcat
    co
    #
    cconcat
    co
    #
    @21
    @74
    cconcat
    co
    #
    @16
    cconcat
    co
    #
    @58
    @39
    @23
    @75
    @21
    cconcat
    @39
    @23
    cM
    @20
    @15
    cconcat
    co
    #
    ccom
    #
    cM
    @20
    ccom
    #
    @16
    cconcat
    co
    #
    @75
    @39
    @22
    @79
    cM
    @39
    @22
    @20
    creverse
    cfv
    #
    @15
    cconcat
    co
    #
    @79
    @39
    @36
    @20
    @1
    wcel
    #
    @22
    @84
    wceq
    @45
    @39
    @19
    @0
    @70
    s1cld
    #
    @0
    @14
    @20
    revccat
    syl2anc
    @83
    @20
    @15
    cconcat
    @19
    revs1
    oveq1i
    syl6eq
    coeq2d
    @39
    @85
    @46
    @47
    @80
    @82
    wceq
    @86
    @48
    @47
    @39
    @49
    a1i
    @0
    @0
    @20
    @15
    cM
    ccatco
    syl3anc
    @39
    @81
    @74
    @16
    cconcat
    @39
    @37
    @47
    @81
    @74
    wceq
    @70
    @49
    @0
    @0
    @19
    cM
    s1co
    sylancl
    oveq1d
    3eqtrd
    oveq2d
    @39
    @21
    @1
    wcel
    #
    @74
    @1
    wcel
    #
    @44
    @78
    @76
    wceq
    @39
    @36
    @85
    @87
    @45
    @86
    @0
    @14
    @20
    ccatcl
    syl2anc
    @39
    @54
    @0
    @71
    s1cld
    #
    @50
    @0
    @21
    @74
    @16
    ccatass
    syl3anc
    @39
    @77
    @57
    @16
    cconcat
    @39
    @77
    @14
    @20
    @74
    cconcat
    co
    #
    cconcat
    co
    #
    @57
    @39
    @36
    @85
    @88
    @77
    @91
    wceq
    @45
    @86
    @89
    @0
    @14
    @20
    @74
    ccatass
    syl3anc
    @55
    @90
    @14
    cconcat
    @19
    @54
    df-s2
    oveq2i
    syl6eqr
    oveq1d
    3eqtr2rd
    3eqtrd
    @39
    @42
    @60
    @0
    cxp
    #
    wfn
    #
    @61
    @37
    @53
    @43
    wcel
    @39
    @41
    @92
    cW
    @42
    wf
    #
    @93
    @51
    @41
    @42
    vm
    vu
    @60
    @0
    @17
    vm
    cv
    #
    @95
    vu
    cv
    #
    @96
    cM
    cfv
    cs2
    cotp
    csplice
    co
    cmpt2
    wceq
    @94
    vy
    vz
    vw
    vv
    c.sm
    cT
    vn
    cI
    cM
    cW
    @17
    vm
    vu
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtf
    simprd
    @92
    cW
    @42
    ffn
    3syl
    @69
    @70
    @60
    @0
    @52
    @19
    @42
    fnovrn
    syl3anc
    eqeltrrd
    vy
    vz
    vw
    vv
    @17
    @24
    c.sm
    cT
    vn
    cI
    cM
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgi2
    syl2anc
    ersym
    @39
    @24
    @17
    c0
    c.sm
    cW
    @40
    ertr
    mpand
    expcom
    a2d
    wrdind
    mpcom
end
