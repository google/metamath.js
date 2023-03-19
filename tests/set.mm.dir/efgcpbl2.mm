include "wbr.mm"
include "wa.mm"
include "cconcat.mm"
include "co.mm"
include "wer.mm"
include "efger.mm"
include "a1i.mm"
include "c0.mm"
include "wcel.mm"
include "simpl.mm"
include "ercl.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "wrd0.mm"
include "cvv.mm"
include "wceq.mm"
include "efgrcl.mm"
include "syl.mm"
include "simprd.mm"
include "syl5eleqr.mm"
include "simpr.mm"
include "efgcpbl.mm"
include "syl3anc.mm"
include "eleqtrd.mm"
include "ccatcl.mm"
include "syl2anc.mm"
include "ccatrid.mm"
include "ercl2.mm"
include "3brtr3d.mm"
include "ccatlid.mm"
include "oveq1d.mm"
include "ertrd.mm"

theorem efgcpbl2
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
  let cX: class X
  let cY: class Y
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
  let cQ: class Q
  let cC: class C
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
  assert |- ( ( A .~ X /\ B .~ Y ) -> ( A ++ B ) .~ ( X ++ Y ) )

  proof
    cA
    cX
    c.sm
    wbr
    #
    cB
    cY
    c.sm
    wbr
    #
    wa
    #
    cA
    cB
    cconcat
    co
    #
    cA
    cY
    cconcat
    co
    #
    cX
    cY
    cconcat
    co
    #
    c.sm
    cW
    cW
    c.sm
    wer
    @2
    c.sm
    cI
    cW
    efgval.w
    efgval.r
    efger
    a1i
    #
    @2
    @3
    c0
    cconcat
    co
    #
    @4
    c0
    cconcat
    co
    #
    @3
    @4
    c.sm
    @2
    cA
    cW
    wcel
    #
    c0
    cW
    wcel
    #
    @1
    @7
    @8
    c.sm
    wbr
    @2
    cA
    cX
    c.sm
    cW
    @6
    @0
    @1
    simpl
    #
    ercl
    #
    @2
    c0
    cI
    c2o
    cxp
    #
    cword
    #
    cW
    @13
    wrd0
    @2
    cI
    cvv
    wcel
    #
    cW
    @14
    wceq
    #
    @2
    @9
    @15
    @16
    wa
    @12
    cA
    cI
    cW
    efgval.w
    efgrcl
    syl
    simprd
    #
    syl5eleqr
    #
    @0
    @1
    simpr
    #
    vx
    vy
    vz
    vw
    vv
    vt
    cA
    c0
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
    cB
    cY
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgcpbl
    syl3anc
    @2
    @3
    @14
    wcel
    #
    @7
    @3
    wceq
    @2
    cA
    @14
    wcel
    #
    cB
    @14
    wcel
    @20
    @2
    cA
    cW
    @14
    @12
    @17
    eleqtrd
    #
    @2
    cB
    cW
    @14
    @2
    cB
    cY
    c.sm
    cW
    @6
    @19
    ercl
    @17
    eleqtrd
    @13
    cA
    cB
    ccatcl
    syl2anc
    @13
    @3
    ccatrid
    syl
    @2
    @4
    @14
    wcel
    #
    @8
    @4
    wceq
    @2
    @21
    cY
    @14
    wcel
    @23
    @22
    @2
    cY
    cW
    @14
    @2
    cB
    cY
    c.sm
    cW
    @6
    @19
    ercl2
    #
    @17
    eleqtrd
    @13
    cA
    cY
    ccatcl
    syl2anc
    @13
    @4
    ccatrid
    syl
    3brtr3d
    @2
    c0
    cA
    cconcat
    co
    #
    cY
    cconcat
    co
    #
    c0
    cX
    cconcat
    co
    #
    cY
    cconcat
    co
    #
    @4
    @5
    c.sm
    @2
    @10
    cY
    cW
    wcel
    @0
    @26
    @28
    c.sm
    wbr
    @18
    @24
    @11
    vx
    vy
    vz
    vw
    vv
    vt
    c0
    cY
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
    cA
    cX
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgcpbl
    syl3anc
    @2
    @25
    cA
    cY
    cconcat
    @2
    @21
    @25
    cA
    wceq
    @22
    @13
    cA
    ccatlid
    syl
    oveq1d
    @2
    @27
    cX
    cY
    cconcat
    @2
    cX
    @14
    wcel
    @27
    cX
    wceq
    @2
    cX
    cW
    @14
    @2
    cA
    cX
    c.sm
    cW
    @6
    @11
    ercl2
    @17
    eleqtrd
    @13
    cX
    ccatlid
    syl
    oveq1d
    3brtr3d
    ertrd
end
