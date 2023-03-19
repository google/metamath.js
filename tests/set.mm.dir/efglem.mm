include "cxp.mm"
include "wer.mm"
include "cv.mm"
include "cop.mm"
include "c1o.mm"
include "cdif.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "co.mm"
include "wbr.mm"
include "c2o.mm"
include "wral.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "wa.mm"
include "wex.mm"
include "xpider.mm"
include "wcel.mm"
include "simpll.mm"
include "cword.mm"
include "cid.mm"
include "fviss.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "opelxpi.mm"
include "adantl.mm"
include "2oconcl.mm"
include "sylan2.mm"
include "s2cld.mm"
include "splcl.mm"
include "syl2anc.mm"
include "wceq.mm"
include "cvv.mm"
include "efgrcl.mm"
include "simprd.mm"
include "ad2antrr.mm"
include "eleqtrrd.mm"
include "brxp.mm"
include "sylanbrc.mm"
include "ralrimivva.mm"
include "rgen2.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "ereq1.mm"
include "breq.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "spcev.mm"
include "mp2an.mm"

theorem efglem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vn: setvar n
  let cI: class I
  let cW: class W
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vs: setvar s
  let vu: setvar u
  let cA: class A
  let cJ: class J
  let cL: class L
  let cF: class F
  let cK: class K
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let cP: class P
  let wph: wff ph
  let vm: setvar m
  let cM: class M
  let cN: class N
  let cU: class U
  let vk: setvar k
  let vo: setvar o
  let cT: class T
  let cV: class V
  let cX: class X
  let cQ: class Q
  let c.sm: class .~
  let cB: class B
  let cC: class C
  let cS: class S
  let cY: class Y
  let cD: class D
  assume efgval.w: |- W = ( _I ` Word ( I X. 2o ) )

  disjoint r y
  disjoint r z
  disjoint y z
  disjoint n y
  disjoint n z
  disjoint n r
  disjoint n x
  disjoint r x
  disjoint W n
  disjoint W r
  disjoint x y
  disjoint x z
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint I n
  disjoint I r
  disjoint I x
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
  disjoint n v
  disjoint n w
  disjoint P n
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint P t
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint P v
  disjoint w y
  disjoint w z
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
  disjoint n s
  disjoint n u
  disjoint M n
  disjoint r t
  disjoint r v
  disjoint r w
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
  disjoint M v
  disjoint w x
  disjoint M w
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
  disjoint s y
  disjoint s z
  disjoint W s
  disjoint W t
  disjoint u y
  disjoint u z
  disjoint W u
  disjoint W v
  disjoint W w
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
  disjoint .~ y
  disjoint .~ z
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
  disjoint I s
  disjoint I t
  disjoint I u
  disjoint I v
  disjoint I w
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
  assert |- E. r ( r Er W /\ A. x e. W A. n e. ( 0 ... ( # ` x ) ) A. y e. I A. z e. 2o x r ( x splice <. n , n , <" <. y , z >. <. y , ( 1o \ z ) >. "> >. ) )

  proof
    cW
    cW
    cW
    cxp
    #
    wer
    #
    vx
    cv
    #
    @2
    vn
    cv
    #
    @3
    vy
    cv
    #
    vz
    cv
    #
    cop
    #
    @4
    c1o
    @5
    cdif
    #
    cop
    #
    cs2
    #
    cotp
    csplice
    co
    #
    @0
    wbr
    #
    vz
    c2o
    wral
    vy
    cI
    wral
    #
    vn
    cc0
    @2
    chash
    cfv
    cfz
    co
    #
    wral
    vx
    cW
    wral
    #
    cW
    vr
    cv
    #
    wer
    #
    @2
    @10
    @15
    wbr
    #
    vz
    c2o
    wral
    vy
    cI
    wral
    #
    vn
    @13
    wral
    vx
    cW
    wral
    #
    wa
    #
    vr
    wex
    cW
    xpider
    @12
    vx
    vn
    cW
    @13
    @2
    cW
    wcel
    #
    @3
    @13
    wcel
    #
    wa
    #
    @11
    vy
    vz
    cI
    c2o
    @23
    @4
    cI
    wcel
    #
    @5
    c2o
    wcel
    #
    wa
    #
    wa
    #
    @21
    @10
    cW
    wcel
    @11
    @21
    @22
    @26
    simpll
    #
    @27
    @10
    cI
    c2o
    cxp
    #
    cword
    #
    cW
    @27
    @2
    @30
    wcel
    @9
    @30
    wcel
    @10
    @30
    wcel
    @27
    cW
    @30
    @2
    cW
    @30
    cid
    cfv
    #
    @30
    efgval.w
    @30
    fviss
    eqsstri
    @28
    sseldi
    @27
    @6
    @8
    @29
    @26
    @6
    @29
    wcel
    @23
    @4
    @5
    cI
    c2o
    opelxpi
    adantl
    @26
    @8
    @29
    wcel
    #
    @23
    @25
    @24
    @7
    c2o
    wcel
    @32
    @5
    2oconcl
    @4
    @7
    cI
    c2o
    opelxpi
    sylan2
    adantl
    s2cld
    @29
    @9
    @2
    @3
    @3
    splcl
    syl2anc
    @21
    cW
    @30
    wceq
    #
    @22
    @26
    @21
    cI
    cvv
    wcel
    @33
    @2
    cI
    cW
    efgval.w
    efgrcl
    simprd
    ad2antrr
    eleqtrrd
    @2
    @10
    cW
    cW
    brxp
    sylanbrc
    ralrimivva
    rgen2
    @20
    @1
    @14
    wa
    vr
    @0
    cW
    cW
    cW
    @31
    cvv
    efgval.w
    @30
    cid
    fvex
    eqeltri
    #
    @34
    xpex
    @15
    @0
    wceq
    #
    @16
    @1
    @19
    @14
    cW
    @15
    @0
    ereq1
    @35
    @18
    @12
    vx
    vn
    cW
    @13
    @35
    @17
    @11
    vy
    vz
    cI
    c2o
    @2
    @10
    @15
    @0
    breq
    2ralbidv
    2ralbidv
    anbi12d
    spcev
    mp2an
end
