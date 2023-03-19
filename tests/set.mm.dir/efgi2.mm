include "wcel.mm"
include "cfv.mm"
include "crn.mm"
include "wa.mm"
include "cop.mm"
include "wbr.mm"
include "cv.mm"
include "wer.mm"
include "cec.mm"
include "wss.mm"
include "wral.mm"
include "cab.mm"
include "cint.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "fveq2.mm"
include "rneqd.mm"
include "eceq1.mm"
include "sseq12d.mm"
include "rspcv.mm"
include "adantr.mm"
include "ssel.mm"
include "com12.mm"
include "simpl.mm"
include "elecg.mm"
include "mpbid.mm"
include "df-br.mm"
include "sylib.mm"
include "expcom.mm"
include "sylan9r.mm"
include "syld.mm"
include "adantld.mm"
include "alrimiv.mm"
include "opex.mm"
include "elintab.mm"
include "sylibr.mm"
include "efgval2.mm"
include "syl6eleqr.mm"

theorem efgi2
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
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
  assert |- ( ( A e. W /\ B e. ran ( T ` A ) ) -> A .~ B )

  proof
    cA
    cW
    wcel
    #
    cB
    cA
    cT
    cfv
    #
    crn
    #
    wcel
    #
    wa
    #
    cA
    cB
    cop
    #
    c.sm
    wcel
    cA
    cB
    c.sm
    wbr
    @4
    @5
    cW
    vr
    cv
    #
    wer
    #
    va
    cv
    #
    cT
    cfv
    #
    crn
    #
    @8
    @6
    cec
    #
    wss
    #
    va
    cW
    wral
    #
    wa
    #
    vr
    cab
    cint
    #
    c.sm
    @4
    @14
    @5
    @6
    wcel
    #
    wi
    #
    vr
    wal
    @5
    @15
    wcel
    @4
    @17
    vr
    @4
    @13
    @16
    @7
    @4
    @13
    @2
    cA
    @6
    cec
    #
    wss
    #
    @16
    @0
    @13
    @19
    wi
    @3
    @12
    @19
    va
    cA
    cW
    @8
    cA
    wceq
    #
    @10
    @2
    @11
    @18
    @20
    @9
    @1
    @8
    cA
    cT
    fveq2
    rneqd
    @8
    cA
    @6
    eceq1
    sseq12d
    rspcv
    adantr
    @3
    @19
    cB
    @18
    wcel
    #
    @0
    @16
    @19
    @3
    @21
    @2
    @18
    cB
    ssel
    com12
    @21
    @0
    @16
    @21
    @0
    wa
    #
    cA
    cB
    @6
    wbr
    #
    @16
    @22
    @21
    @23
    @21
    @0
    simpl
    cB
    cA
    @6
    @18
    cW
    elecg
    mpbid
    cA
    cB
    @6
    df-br
    sylib
    expcom
    sylan9r
    syld
    adantld
    alrimiv
    @14
    vr
    @5
    cA
    cB
    opex
    elintab
    sylibr
    va
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
    vr
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgval2
    syl6eleqr
    cA
    cB
    c.sm
    df-br
    sylibr
end
