include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "wrmo.mm"
include "wreu.mm"
include "wfo.mm"
include "wf.mm"
include "efgsfo.mm"
include "fof.mm"
include "ax-mp.mm"
include "ffvelrni.mm"
include "ad2antlr.mm"
include "efgredeu.mm"
include "reurmo.mm"
include "3syl.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "crn.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "efgsdm.mm"
include "simp2bi.mm"
include "ad2antrr.mm"
include "wer.mm"
include "efger.mm"
include "a1i.mm"
include "efgsrel.mm"
include "simpr.mm"
include "ertrd.mm"
include "breq1.mm"
include "rmoi.mm"
include "syl122anc.mm"
include "eqbrtrd.mm"
include "ertr3d.mm"
include "impbida.mm"

theorem efgred2
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
  let wph: wff ph
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
  disjoint k m
  disjoint k t
  disjoint k x
  disjoint T k
  disjoint T m
  disjoint T t
  disjoint T x
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
  disjoint .~ m
  disjoint .~ t
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint I m
  disjoint I n
  disjoint I t
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
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
  disjoint .~ i
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
  disjoint I r
  disjoint I s
  disjoint I u
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D r
  disjoint D s
  disjoint D u
  assert |- ( ( A e. dom S /\ B e. dom S ) -> ( ( S ` A ) .~ ( S ` B ) <-> ( A ` 0 ) = ( B ` 0 ) ) )

  proof
    cA
    cS
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cS
    cfv
    #
    cB
    cS
    cfv
    #
    c.sm
    wbr
    #
    cc0
    cA
    cfv
    #
    cc0
    cB
    cfv
    #
    wceq
    #
    @3
    @6
    wa
    #
    vd
    cv
    #
    @5
    c.sm
    wbr
    #
    vd
    cD
    wrmo
    #
    @7
    cD
    wcel
    #
    @7
    @5
    c.sm
    wbr
    #
    @8
    cD
    wcel
    #
    @8
    @5
    c.sm
    wbr
    #
    @9
    @10
    @5
    cW
    wcel
    #
    @12
    vd
    cD
    wreu
    @13
    @2
    @18
    @1
    @6
    @0
    cW
    cB
    cS
    @0
    cW
    cS
    wfo
    @0
    cW
    cS
    wf
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
    efgsfo
    @0
    cW
    cS
    fof
    ax-mp
    ffvelrni
    ad2antlr
    vx
    vy
    vz
    vw
    vv
    vt
    @5
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
    vd
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgredeu
    @12
    vd
    cD
    reurmo
    3syl
    @1
    @14
    @2
    @6
    @1
    cA
    cW
    cword
    c0
    csn
    cdif
    #
    wcel
    @14
    vi
    cv
    #
    cA
    cfv
    @20
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
    vi
    c1
    cA
    chash
    cfv
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
    vi
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
    simp2bi
    ad2antrr
    @10
    @7
    @4
    @5
    c.sm
    cW
    cW
    c.sm
    wer
    #
    @10
    c.sm
    cI
    cW
    efgval.w
    efgval.r
    efger
    #
    a1i
    @1
    @7
    @4
    c.sm
    wbr
    #
    @2
    @6
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
    efgsrel
    #
    ad2antrr
    @3
    @6
    simpr
    ertrd
    @2
    @16
    @1
    @6
    @2
    cB
    @19
    wcel
    @16
    @20
    cB
    cfv
    @21
    cB
    cfv
    cT
    cfv
    crn
    wcel
    vi
    c1
    cB
    chash
    cfv
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
    vi
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
    simp2bi
    ad2antlr
    @2
    @17
    @1
    @6
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
    efgsrel
    #
    ad2antlr
    @12
    @15
    @17
    vd
    cD
    @7
    @8
    @11
    @7
    @5
    c.sm
    breq1
    @11
    @8
    @5
    c.sm
    breq1
    rmoi
    syl122anc
    @3
    @9
    wa
    #
    @4
    @7
    @5
    c.sm
    cW
    @22
    @27
    @23
    a1i
    @1
    @24
    @2
    @9
    @25
    ad2antrr
    @27
    @7
    @8
    @5
    c.sm
    @3
    @9
    simpr
    @2
    @17
    @1
    @9
    @26
    ad2antlr
    eqbrtrd
    ertr3d
    impbida
end
