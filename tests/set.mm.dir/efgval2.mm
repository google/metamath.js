include "cv.mm"
include "wer.mm"
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
include "cab.mm"
include "cint.mm"
include "crn.mm"
include "cec.mm"
include "wss.mm"
include "efgval.mm"
include "wcel.mm"
include "cxp.mm"
include "cmpt2.mm"
include "wceq.mm"
include "wf.mm"
include "efgtf.mm"
include "simpld.mm"
include "rneqd.mm"
include "sseq1d.mm"
include "dfss3.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "rgen2w.mm"
include "eqid.mm"
include "vex.mm"
include "elec.mm"
include "breq2.mm"
include "syl5bb.mm"
include "ralrnmpt2.mm"
include "ax-mp.mm"
include "id.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "s2eqd.mm"
include "oteq3d.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "ralxp.mm"
include "eqidd.mm"
include "efgmval.mm"
include "ralbidva.mm"
include "ralbiia.mm"
include "bitri.mm"
include "ralbii.mm"
include "syl6bb.mm"
include "anbi2i.mm"
include "abbii.mm"
include "inteqi.mm"
include "eqtr4i.mm"

theorem efgval2
  let vx: setvar x
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
  let cP: class P
  let wph: wff ph
  let vm: setvar m
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

  disjoint r y
  disjoint r z
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
  disjoint n r
  disjoint n x
  disjoint M n
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint M r
  disjoint v x
  disjoint M v
  disjoint w x
  disjoint M w
  disjoint M x
  disjoint T r
  disjoint T x
  disjoint W n
  disjoint W r
  disjoint W v
  disjoint W w
  disjoint x y
  disjoint x z
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint .~ r
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint I n
  disjoint I r
  disjoint I v
  disjoint I w
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
  disjoint n s
  disjoint n u
  disjoint r t
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
  disjoint T s
  disjoint T t
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
  disjoint .~ a
  disjoint .~ b
  disjoint .~ c
  disjoint .~ d
  disjoint .~ f
  disjoint .~ g
  disjoint .~ i
  disjoint .~ j
  disjoint .~ m
  disjoint .~ s
  disjoint .~ t
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
  disjoint I m
  disjoint I s
  disjoint I t
  disjoint I u
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
  assert |- .~ = |^| { r | ( r Er W /\ A. x e. W ran ( T ` x ) C_ [ x ] r ) }

  proof
    c.sm
    cW
    vr
    cv
    #
    wer
    #
    vx
    cv
    #
    @2
    vm
    cv
    #
    @3
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    @4
    c1o
    @5
    cdif
    cop
    #
    cs2
    #
    cotp
    #
    csplice
    co
    #
    @0
    wbr
    #
    vb
    c2o
    wral
    #
    va
    cI
    wral
    #
    vm
    cc0
    @2
    chash
    cfv
    cfz
    co
    #
    wral
    #
    vx
    cW
    wral
    #
    wa
    #
    vr
    cab
    #
    cint
    @1
    @2
    cT
    cfv
    #
    crn
    #
    @2
    @0
    cec
    #
    wss
    #
    vx
    cW
    wral
    #
    wa
    #
    vr
    cab
    #
    cint
    vx
    va
    vb
    c.sm
    vm
    cI
    cW
    vr
    efgval.w
    efgval.r
    efgval
    @25
    @18
    @24
    @17
    vr
    @23
    @16
    @1
    @22
    @15
    vx
    cW
    @2
    cW
    wcel
    #
    @22
    vm
    vu
    @14
    cI
    c2o
    cxp
    #
    @2
    @3
    @3
    vu
    cv
    #
    @28
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
    crn
    #
    @21
    wss
    #
    @15
    @26
    @20
    @34
    @21
    @26
    @19
    @33
    @26
    @19
    @33
    wceq
    @14
    @27
    cxp
    cW
    @19
    wf
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
    @2
    vm
    vu
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgtf
    simpld
    rneqd
    sseq1d
    @35
    @4
    @21
    wcel
    #
    va
    @34
    wral
    #
    @15
    va
    @34
    @21
    dfss3
    @37
    @2
    @32
    @0
    wbr
    #
    vu
    @27
    wral
    #
    vm
    @14
    wral
    #
    @15
    @32
    cvv
    wcel
    #
    vu
    @27
    wral
    vm
    @14
    wral
    @37
    @40
    wb
    @41
    vm
    vu
    @14
    @27
    @2
    @31
    csplice
    ovex
    rgen2w
    @36
    @38
    vm
    vu
    va
    @14
    @27
    @32
    @33
    cvv
    @33
    eqid
    @36
    @2
    @4
    @0
    wbr
    @4
    @32
    wceq
    @38
    @4
    @2
    @0
    va
    vex
    vx
    vex
    elec
    @4
    @32
    @2
    @0
    breq2
    syl5bb
    ralrnmpt2
    ax-mp
    @39
    @13
    vm
    @14
    @39
    @2
    @2
    @3
    @3
    @6
    @4
    @5
    cM
    co
    #
    cs2
    #
    cotp
    #
    csplice
    co
    #
    @0
    wbr
    #
    vb
    c2o
    wral
    #
    va
    cI
    wral
    @13
    @38
    @46
    vu
    va
    vb
    cI
    c2o
    @28
    @6
    wceq
    #
    @32
    @45
    @2
    @0
    @48
    @31
    @44
    @2
    csplice
    @48
    @30
    @43
    @3
    @3
    @48
    @28
    @29
    @6
    @42
    @48
    id
    @48
    @29
    @6
    cM
    cfv
    @42
    @28
    @6
    cM
    fveq2
    @4
    @5
    cM
    df-ov
    syl6eqr
    s2eqd
    oteq3d
    oveq2d
    breq2d
    ralxp
    @47
    @12
    va
    cI
    @4
    cI
    wcel
    #
    @46
    @11
    vb
    c2o
    @49
    @5
    c2o
    wcel
    wa
    #
    @45
    @10
    @2
    @0
    @50
    @44
    @9
    @2
    csplice
    @50
    @43
    @8
    @3
    @3
    @50
    @6
    @42
    @6
    @7
    @50
    @6
    eqidd
    vy
    vz
    @4
    @5
    cI
    cM
    efgval2.m
    efgmval
    s2eqd
    oteq3d
    oveq2d
    breq2d
    ralbidva
    ralbiia
    bitri
    ralbii
    bitri
    bitri
    syl6bb
    ralbiia
    anbi2i
    abbii
    inteqi
    eqtr4i
end
