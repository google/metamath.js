include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "wceq.mm"
include "wn.mm"
include "cc0.mm"
include "wa.mm"
include "cdm.mm"
include "efgsval.mm"
include "syl.mm"
include "eqtr3d.mm"
include "oveq1.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "sylan9eq.mm"
include "eleq1d.mm"
include "wb.mm"
include "efgs1b.mm"
include "3bitr3d.mm"
include "biimpa.mm"
include "mtand.mm"
include "wo.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "crn.mm"
include "cfzo.mm"
include "wral.mm"
include "efgsdm.mm"
include "simp1bi.mm"
include "wne.mm"
include "eldifsn.mm"
include "lennncl.mm"
include "sylbi.mm"
include "3syl.mm"
include "elnn1uz2.mm"
include "sylib.mm"
include "ord.mm"
include "mpd.mm"
include "uz2m1nn.mm"
include "mtbid.mm"
include "jca.mm"

theorem efgredlema
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let c.sm: class .~
  let cS: class S
  let cT: class T
  let vk: setvar k
  let vm: setvar m
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
  let cP: class P
  let cN: class N
  let cU: class U
  let vo: setvar o
  let cV: class V
  let cX: class X
  let cQ: class Q
  let cC: class C
  let cY: class Y
  assume efgval.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume efgval.r: |- .~ = ( ~FG ` I )
  assume efgval2.m: |- M = ( y e. I , z e. 2o |-> <. y , ( 1o \ z ) >. )
  assume efgval2.t: |- T = ( v e. W |-> ( n e. ( 0 ... ( # ` v ) ) , w e. ( I X. 2o ) |-> ( v splice <. n , n , <" w ( M ` w ) "> >. ) ) )
  assume efgred.d: |- D = ( W \ U_ x e. W ran ( T ` x ) )
  assume efgred.s: |- S = ( m e. { t e. ( Word W \ { (/) } ) | ( ( t ` 0 ) e. D /\ A. k e. ( 1 ..^ ( # ` t ) ) ( t ` k ) e. ran ( T ` ( t ` ( k - 1 ) ) ) ) } |-> ( m ` ( ( # ` m ) - 1 ) ) )
  assume efgredlem.1: |- ( ph -> A. a e. dom S A. b e. dom S ( ( # ` ( S ` a ) ) < ( # ` ( S ` A ) ) -> ( ( S ` a ) = ( S ` b ) -> ( a ` 0 ) = ( b ` 0 ) ) ) )
  assume efgredlem.2: |- ( ph -> A e. dom S )
  assume efgredlem.3: |- ( ph -> B e. dom S )
  assume efgredlem.4: |- ( ph -> ( S ` A ) = ( S ` B ) )
  assume efgredlem.5: |- ( ph -> -. ( A ` 0 ) = ( B ` 0 ) )

  disjoint a b
  disjoint A a
  disjoint A b
  disjoint a y
  disjoint a z
  disjoint b y
  disjoint b z
  disjoint y z
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
  disjoint a k
  disjoint T a
  disjoint b k
  disjoint T b
  disjoint k m
  disjoint k t
  disjoint k x
  disjoint T k
  disjoint T m
  disjoint T t
  disjoint T x
  disjoint W a
  disjoint W b
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
  disjoint .~ a
  disjoint .~ b
  disjoint .~ m
  disjoint .~ t
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint B a
  disjoint B b
  disjoint S a
  disjoint S b
  disjoint I a
  disjoint I b
  disjoint I m
  disjoint I n
  disjoint I t
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint D a
  disjoint D b
  disjoint D m
  disjoint D t
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
  disjoint a o
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
  disjoint .~ c
  disjoint .~ d
  disjoint .~ f
  disjoint .~ g
  disjoint .~ i
  disjoint .~ j
  disjoint .~ r
  disjoint .~ s
  disjoint .~ u
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
  disjoint I r
  disjoint I s
  disjoint I u
  disjoint D c
  disjoint D d
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D r
  disjoint D s
  disjoint D u
  assert |- ( ph -> ( ( ( # ` A ) - 1 ) e. NN /\ ( ( # ` B ) - 1 ) e. NN ) )

  proof
    wph
    cA
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cn
    wcel
    #
    cB
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cn
    wcel
    #
    wph
    @0
    c2
    cuz
    cfv
    #
    wcel
    #
    @2
    wph
    @0
    c1
    wceq
    #
    wn
    @7
    wph
    @8
    cc0
    cA
    cfv
    #
    cc0
    cB
    cfv
    #
    wceq
    efgredlem.5
    wph
    @8
    wa
    #
    @4
    cB
    cfv
    #
    @9
    @10
    wph
    @8
    @12
    @1
    cA
    cfv
    #
    @9
    wph
    cB
    cS
    cfv
    #
    @12
    @13
    wph
    cB
    cS
    cdm
    #
    wcel
    #
    @14
    @12
    wceq
    efgredlem.3
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
    cB
    cI
    cM
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgsval
    syl
    wph
    cA
    cS
    cfv
    #
    @14
    @13
    efgredlem.4
    wph
    cA
    @15
    wcel
    #
    @17
    @13
    wceq
    efgredlem.2
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
    cA
    cI
    cM
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgsval
    syl
    eqtr3d
    eqtr3d
    @8
    @1
    cc0
    cA
    @8
    @1
    c1
    c1
    cmin
    co
    #
    cc0
    @0
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    fveq2d
    sylan9eq
    @11
    @3
    c1
    wceq
    #
    @12
    @10
    wceq
    wph
    @8
    @20
    wph
    @17
    cD
    wcel
    #
    @14
    cD
    wcel
    #
    @8
    @20
    wph
    @17
    @14
    cD
    efgredlem.4
    eleq1d
    wph
    @18
    @21
    @8
    wb
    efgredlem.2
    vx
    vy
    vz
    vw
    vv
    vt
    cA
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
    efgs1b
    syl
    wph
    @16
    @22
    @20
    wb
    efgredlem.3
    vx
    vy
    vz
    vw
    vv
    vt
    cB
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
    efgs1b
    syl
    3bitr3d
    #
    biimpa
    @20
    @4
    cc0
    cB
    @20
    @4
    @19
    cc0
    @3
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    fveq2d
    syl
    eqtr3d
    mtand
    #
    wph
    @8
    @7
    wph
    @0
    cn
    wcel
    #
    @8
    @7
    wo
    wph
    @18
    cA
    cW
    cword
    #
    c0
    csn
    cdif
    #
    wcel
    #
    @25
    efgredlem.2
    @18
    @28
    @9
    cD
    wcel
    vu
    cv
    #
    cA
    cfv
    @29
    c1
    cmin
    co
    #
    cA
    cfv
    cT
    cfv
    crn
    wcel
    vu
    c1
    @0
    cfzo
    co
    wral
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
    vu
    vk
    vm
    vn
    cA
    cI
    cM
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgsdm
    simp1bi
    @28
    cA
    @26
    wcel
    cA
    c0
    wne
    wa
    @25
    cA
    @26
    c0
    eldifsn
    cW
    cA
    lennncl
    sylbi
    3syl
    @0
    elnn1uz2
    sylib
    ord
    mpd
    @0
    uz2m1nn
    syl
    wph
    @3
    @6
    wcel
    #
    @5
    wph
    @20
    wn
    @31
    wph
    @8
    @20
    @24
    @23
    mtbid
    wph
    @20
    @31
    wph
    @3
    cn
    wcel
    #
    @20
    @31
    wo
    wph
    @16
    cB
    @27
    wcel
    #
    @32
    efgredlem.3
    @16
    @33
    @10
    cD
    wcel
    @29
    cB
    cfv
    @30
    cB
    cfv
    cT
    cfv
    crn
    wcel
    vu
    c1
    @3
    cfzo
    co
    wral
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
    vu
    vk
    vm
    vn
    cB
    cI
    cM
    cW
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgsdm
    simp1bi
    @33
    cB
    @26
    wcel
    cB
    c0
    wne
    wa
    @32
    cB
    @26
    c0
    eldifsn
    cW
    cB
    lennncl
    sylbi
    3syl
    @3
    elnn1uz2
    sylib
    ord
    mpd
    @3
    uz2m1nn
    syl
    jca
end
