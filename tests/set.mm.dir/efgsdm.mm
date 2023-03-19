include "cdm.mm"
include "wcel.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cc0.mm"
include "cfv.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "crn.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "w3a.mm"
include "wceq.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "rneqd.mm"
include "eleq12d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "crab.mm"
include "efgsf.mm"
include "fdmi.mm"
include "oveq1.mm"
include "cbvralv.mm"
include "syl5bb.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem efgsdm
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let cD: class D
  let c.sm: class .~
  let cS: class S
  let cT: class T
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
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
  let vj: setvar j
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  let cA: class A
  let cJ: class J
  let cL: class L
  let cK: class K
  let cP: class P
  let wph: wff ph
  let cN: class N
  let cU: class U
  let vo: setvar o
  let cV: class V
  let cX: class X
  let cQ: class Q
  let cB: class B
  let cC: class C
  let cY: class Y
  assume efgval.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume efgval.r: |- .~ = ( ~FG ` I )
  assume efgval2.m: |- M = ( y e. I , z e. 2o |-> <. y , ( 1o \ z ) >. )
  assume efgval2.t: |- T = ( v e. W |-> ( n e. ( 0 ... ( # ` v ) ) , w e. ( I X. 2o ) |-> ( v splice <. n , n , <" w ( M ` w ) "> >. ) ) )
  assume efgred.d: |- D = ( W \ U_ x e. W ran ( T ` x ) )
  assume efgred.s: |- S = ( m e. { t e. ( Word W \ { (/) } ) | ( ( t ` 0 ) e. D /\ A. k e. ( 1 ..^ ( # ` t ) ) ( t ` k ) e. ran ( T ` ( t ` ( k - 1 ) ) ) ) } |-> ( m ` ( ( # ` m ) - 1 ) ) )

  disjoint y z
  disjoint F i
  disjoint n t
  disjoint n v
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint w y
  disjoint w z
  disjoint i m
  disjoint i n
  disjoint i t
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint M i
  disjoint m n
  disjoint m t
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint M m
  disjoint n x
  disjoint M n
  disjoint t x
  disjoint M t
  disjoint v x
  disjoint M v
  disjoint w x
  disjoint M w
  disjoint M x
  disjoint i k
  disjoint T i
  disjoint k m
  disjoint k t
  disjoint k x
  disjoint T k
  disjoint T m
  disjoint T t
  disjoint T x
  disjoint i y
  disjoint i z
  disjoint W i
  disjoint k n
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint W k
  disjoint m y
  disjoint m z
  disjoint W m
  disjoint W n
  disjoint W t
  disjoint W v
  disjoint W w
  disjoint x y
  disjoint x z
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint .~ i
  disjoint .~ m
  disjoint .~ t
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint S i
  disjoint I i
  disjoint I m
  disjoint I n
  disjoint I t
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint D i
  disjoint D m
  disjoint D t
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
  disjoint P n
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
  disjoint j m
  disjoint j n
  disjoint j t
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint M j
  disjoint m r
  disjoint m s
  disjoint m u
  disjoint n r
  disjoint n s
  disjoint n u
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
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint M u
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
  disjoint i o
  disjoint j k
  disjoint j o
  disjoint T j
  disjoint k o
  disjoint k r
  disjoint k s
  disjoint k u
  disjoint m o
  disjoint o r
  disjoint o s
  disjoint o t
  disjoint o u
  disjoint o x
  disjoint T o
  disjoint T r
  disjoint T s
  disjoint T u
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
  disjoint j y
  disjoint j z
  disjoint W j
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
  disjoint u y
  disjoint u z
  disjoint W u
  disjoint .~ a
  disjoint .~ b
  disjoint .~ c
  disjoint .~ d
  disjoint .~ f
  disjoint .~ g
  disjoint .~ j
  disjoint .~ r
  disjoint .~ s
  disjoint .~ u
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
  disjoint I j
  disjoint I r
  disjoint I s
  disjoint I u
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D f
  disjoint D j
  disjoint D r
  disjoint D s
  disjoint D u
  assert |- ( F e. dom S <-> ( F e. ( Word W \ { (/) } ) /\ ( F ` 0 ) e. D /\ A. i e. ( 1 ..^ ( # ` F ) ) ( F ` i ) e. ran ( T ` ( F ` ( i - 1 ) ) ) ) )

  proof
    cF
    cS
    cdm
    #
    wcel
    cF
    cW
    cword
    c0
    csn
    cdif
    #
    wcel
    #
    cc0
    cF
    cfv
    #
    cD
    wcel
    #
    vi
    cv
    #
    cF
    cfv
    #
    @5
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cT
    cfv
    #
    crn
    #
    wcel
    #
    vi
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    wa
    #
    wa
    @2
    @4
    @14
    w3a
    cc0
    vf
    cv
    #
    cfv
    #
    cD
    wcel
    #
    @5
    @16
    cfv
    #
    @7
    @16
    cfv
    #
    cT
    cfv
    #
    crn
    #
    wcel
    #
    vi
    c1
    @16
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    wa
    #
    @15
    vf
    cF
    @1
    @0
    @16
    cF
    wceq
    #
    @18
    @4
    @26
    @14
    @28
    @17
    @3
    cD
    cc0
    @16
    cF
    fveq1
    eleq1d
    @28
    @23
    @11
    vi
    @25
    @13
    @28
    @24
    @12
    c1
    cfzo
    @16
    cF
    chash
    fveq2
    oveq2d
    @28
    @19
    @6
    @22
    @10
    @5
    @16
    cF
    fveq1
    @28
    @21
    @9
    @28
    @20
    @8
    cT
    @7
    @16
    cF
    fveq1
    fveq2d
    rneqd
    eleq12d
    raleqbidv
    anbi12d
    @0
    cc0
    vt
    cv
    #
    cfv
    #
    cD
    wcel
    #
    vk
    cv
    #
    @29
    cfv
    #
    @32
    c1
    cmin
    co
    #
    @29
    cfv
    #
    cT
    cfv
    #
    crn
    #
    wcel
    #
    vk
    c1
    @29
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    wa
    #
    vt
    @1
    crab
    #
    @27
    vf
    @1
    crab
    @43
    cW
    cS
    vx
    vy
    vz
    vw
    vv
    vt
    cD
    c.sm
    cS
    cT
    vk
    vm
    vn
    cI
    cM
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgsf
    fdmi
    @42
    @27
    vt
    vf
    @1
    @29
    @16
    wceq
    #
    @31
    @18
    @41
    @26
    @44
    @30
    @17
    cD
    cc0
    @29
    @16
    fveq1
    eleq1d
    @41
    @5
    @29
    cfv
    #
    @7
    @29
    cfv
    #
    cT
    cfv
    #
    crn
    #
    wcel
    #
    vi
    @40
    wral
    @44
    @26
    @38
    @49
    vk
    vi
    @40
    @32
    @5
    wceq
    #
    @33
    @45
    @37
    @48
    @32
    @5
    @29
    fveq2
    @50
    @36
    @47
    @50
    @35
    @46
    cT
    @50
    @34
    @7
    @29
    @32
    @5
    c1
    cmin
    oveq1
    fveq2d
    fveq2d
    rneqd
    eleq12d
    cbvralv
    @44
    @49
    @23
    vi
    @40
    @25
    @44
    @39
    @24
    c1
    cfzo
    @29
    @16
    chash
    fveq2
    oveq2d
    @44
    @45
    @19
    @48
    @22
    @5
    @29
    @16
    fveq1
    @44
    @47
    @21
    @44
    @46
    @20
    cT
    @7
    @29
    @16
    fveq1
    fveq2d
    rneqd
    eleq12d
    raleqbidv
    syl5bb
    anbi12d
    cbvrabv
    eqtri
    elrab2
    @2
    @4
    @14
    3anass
    bitr4i
end
