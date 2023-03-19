include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "c2o.mm"
include "cxp.mm"
include "cv.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "cmpt2.mm"
include "wceq.mm"
include "wf.mm"
include "cvv.mm"
include "wral.mm"
include "wa.mm"
include "cword.mm"
include "cid.mm"
include "fviss.mm"
include "eqsstri.mm"
include "simpl.mm"
include "sseldi.mm"
include "simprr.mm"
include "efgmf.mm"
include "ffvelrni.mm"
include "ad2antll.mm"
include "s2cld.mm"
include "splcl.mm"
include "syl2anc.mm"
include "efgrcl.mm"
include "simprd.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fmpt2.mm"
include "sylib.mm"
include "ovex.mm"
include "con0.mm"
include "simpld.mm"
include "2on.mm"
include "xpexg.mm"
include "sylancl.mm"
include "sylancr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fex2.mm"
include "syl3anc.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqidd.mm"
include "oveq1.mm"
include "mpt2eq123dv.mm"
include "cmpt.mm"
include "weq.mm"
include "oteq1.mm"
include "oteq2.mm"
include "eqtrd.mm"
include "id.mm"
include "s2eqd.mm"
include "oteq3d.mm"
include "cbvmpt2v.mm"
include "syl5eq.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fvmptg.mm"
include "mpdan.mm"
include "feq1d.mm"
include "mpbird.mm"
include "jca.mm"

theorem efgtf
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let c.sm: class .~
  let cT: class T
  let vn: setvar n
  let cI: class I
  let cM: class M
  let cW: class W
  let cX: class X
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
  let cA: class A
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

  disjoint a b
  disjoint a y
  disjoint a z
  disjoint b y
  disjoint b z
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
  disjoint a n
  disjoint a v
  disjoint a w
  disjoint M a
  disjoint b n
  disjoint b v
  disjoint b w
  disjoint M b
  disjoint M n
  disjoint M v
  disjoint M w
  disjoint T a
  disjoint T b
  disjoint X a
  disjoint X b
  disjoint W a
  disjoint W b
  disjoint W n
  disjoint W v
  disjoint W w
  disjoint W y
  disjoint W z
  disjoint .~ a
  disjoint .~ b
  disjoint .~ y
  disjoint .~ z
  disjoint I a
  disjoint I b
  disjoint I n
  disjoint I v
  disjoint I w
  disjoint I y
  disjoint I z
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
  disjoint J a
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
  disjoint a t
  disjoint a x
  disjoint b m
  disjoint b t
  disjoint b x
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
  disjoint b k
  disjoint b o
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
  assert |- ( X e. W -> ( ( T ` X ) = ( a e. ( 0 ... ( # ` X ) ) , b e. ( I X. 2o ) |-> ( X splice <. a , a , <" b ( M ` b ) "> >. ) ) /\ ( T ` X ) : ( ( 0 ... ( # ` X ) ) X. ( I X. 2o ) ) --> W ) )

  proof
    cX
    cW
    wcel
    #
    cX
    cT
    cfv
    #
    va
    vb
    cc0
    cX
    chash
    cfv
    #
    cfz
    co
    #
    cI
    c2o
    cxp
    #
    cX
    va
    cv
    #
    @5
    vb
    cv
    #
    @6
    cM
    cfv
    #
    cs2
    #
    cotp
    #
    csplice
    co
    #
    cmpt2
    #
    wceq
    #
    @3
    @4
    cxp
    #
    cW
    @1
    wf
    #
    @0
    @11
    cvv
    wcel
    #
    @12
    @0
    @13
    cW
    @11
    wf
    #
    @13
    cvv
    wcel
    #
    cW
    cvv
    wcel
    #
    @15
    @0
    @10
    cW
    wcel
    #
    vb
    @4
    wral
    va
    @3
    wral
    @16
    @0
    @19
    va
    vb
    @3
    @4
    @0
    @5
    @3
    wcel
    #
    @6
    @4
    wcel
    #
    wa
    #
    wa
    #
    @10
    @4
    cword
    #
    cW
    @23
    cX
    @24
    wcel
    @8
    @24
    wcel
    @10
    @24
    wcel
    @23
    cW
    @24
    cX
    cW
    @24
    cid
    cfv
    #
    @24
    efgval.w
    @24
    fviss
    eqsstri
    @0
    @22
    simpl
    sseldi
    @23
    @6
    @7
    @4
    @0
    @20
    @21
    simprr
    @21
    @7
    @4
    wcel
    @0
    @20
    @4
    @4
    @6
    cM
    vy
    vz
    cI
    cM
    efgval2.m
    efgmf
    ffvelrni
    ad2antll
    s2cld
    @4
    @8
    cX
    @5
    @5
    splcl
    syl2anc
    @0
    cW
    @24
    wceq
    #
    @22
    @0
    cI
    cvv
    wcel
    #
    @26
    cX
    cI
    cW
    efgval.w
    efgrcl
    #
    simprd
    adantr
    eleqtrrd
    ralrimivva
    va
    vb
    @3
    @4
    @10
    cW
    @11
    @11
    eqid
    fmpt2
    sylib
    #
    @0
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    #
    @17
    cc0
    @2
    cfz
    ovex
    @0
    @27
    c2o
    con0
    wcel
    @30
    @0
    @27
    @26
    @28
    simpld
    2on
    cI
    c2o
    cvv
    con0
    xpexg
    sylancl
    @3
    @4
    cvv
    cvv
    xpexg
    sylancr
    @18
    @0
    cW
    @25
    cvv
    efgval.w
    @24
    cid
    fvex
    eqeltri
    a1i
    @13
    cW
    @11
    cvv
    cvv
    fex2
    syl3anc
    vu
    cX
    va
    vb
    cc0
    vu
    cv
    #
    chash
    cfv
    #
    cfz
    co
    #
    @4
    @31
    @9
    csplice
    co
    #
    cmpt2
    #
    @11
    cW
    cvv
    cT
    @31
    cX
    wceq
    #
    va
    vb
    @33
    @4
    @34
    @3
    @4
    @10
    @36
    @32
    @2
    cc0
    cfz
    @31
    cX
    chash
    fveq2
    oveq2d
    @36
    @4
    eqidd
    @31
    cX
    @9
    csplice
    oveq1
    mpt2eq123dv
    cT
    vv
    cW
    vn
    vw
    cc0
    vv
    cv
    #
    chash
    cfv
    #
    cfz
    co
    #
    @4
    @37
    vn
    cv
    #
    @40
    vw
    cv
    #
    @41
    cM
    cfv
    #
    cs2
    #
    cotp
    #
    csplice
    co
    #
    cmpt2
    #
    cmpt
    vu
    cW
    @35
    cmpt
    efgval2.t
    vv
    vu
    cW
    @46
    @35
    vv
    vu
    weq
    #
    @46
    va
    vb
    @39
    @4
    @37
    @9
    csplice
    co
    #
    cmpt2
    @35
    vn
    vw
    va
    vb
    @39
    @4
    @45
    @48
    @37
    @5
    @5
    @43
    cotp
    #
    csplice
    co
    vn
    va
    weq
    #
    @44
    @49
    @37
    csplice
    @50
    @44
    @5
    @40
    @43
    cotp
    @49
    @40
    @5
    @40
    @43
    oteq1
    @40
    @5
    @5
    @43
    oteq2
    eqtrd
    oveq2d
    vw
    vb
    weq
    #
    @49
    @9
    @37
    csplice
    @51
    @43
    @8
    @5
    @5
    @51
    @41
    @42
    @6
    @7
    @51
    id
    @41
    @6
    cM
    fveq2
    s2eqd
    oteq3d
    oveq2d
    cbvmpt2v
    @47
    va
    vb
    @39
    @4
    @48
    @33
    @4
    @34
    @47
    @38
    @32
    cc0
    cfz
    @37
    @31
    chash
    fveq2
    oveq2d
    @47
    @4
    eqidd
    @37
    @31
    @9
    csplice
    oveq1
    mpt2eq123dv
    syl5eq
    cbvmptv
    eqtri
    fvmptg
    mpdan
    #
    @0
    @14
    @16
    @29
    @0
    @13
    cW
    @1
    @11
    @52
    feq1d
    mpbird
    jca
end
