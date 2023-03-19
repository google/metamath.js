include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "cv.mm"
include "crn.mm"
include "ciun.mm"
include "wn.mm"
include "cdif.mm"
include "eldifn.mm"
include "eleq2s.mm"
include "c2.mm"
include "cuz.mm"
include "cn.mm"
include "wo.mm"
include "cword.mm"
include "c0.mm"
include "csn.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "wral.mm"
include "efgsdm.mm"
include "simp1bi.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "lennncl.mm"
include "sylbi.mm"
include "syl.mm"
include "elnn1uz2.mm"
include "sylib.mm"
include "ord.mm"
include "wf.mm"
include "eldifad.mm"
include "adantr.mm"
include "wrdf.mm"
include "cfz.mm"
include "cz.mm"
include "caddc.mm"
include "1z.mm"
include "simpr.mm"
include "df-2.mm"
include "fveq2i.mm"
include "syl6eleq.mm"
include "eluzp1m1.mm"
include "sylancr.mm"
include "nnuz.mm"
include "syl6eleqr.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "fzoend.mm"
include "elfzofz.mm"
include "3syl.mm"
include "eluzelz.mm"
include "adantl.mm"
include "fzoval.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "uz2m1nn.mm"
include "efgsdmi.mm"
include "sylan2.mm"
include "fveq2.mm"
include "rneqd.mm"
include "eliuni.mm"
include "syl2anc.mm"
include "weq.mm"
include "cbviunv.mm"
include "ex.mm"
include "syld.mm"
include "con1d.mm"
include "syl5.mm"
include "simp2bi.mm"
include "oveq1.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "efgsval.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem efgs1b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let cA: class A
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
  assert |- ( A e. dom S -> ( ( S ` A ) e. D <-> ( # ` A ) = 1 ) )

  proof
    cA
    cS
    cdm
    wcel
    #
    cA
    cS
    cfv
    #
    cD
    wcel
    #
    cA
    chash
    cfv
    #
    c1
    wceq
    #
    @2
    @1
    vx
    cW
    vx
    cv
    #
    cT
    cfv
    #
    crn
    #
    ciun
    #
    wcel
    #
    wn
    #
    @0
    @4
    @10
    @1
    cW
    @8
    cdif
    cD
    @1
    cW
    @8
    eldifn
    efgred.d
    eleq2s
    @0
    @4
    @9
    @0
    @4
    wn
    @3
    c2
    cuz
    cfv
    #
    wcel
    #
    @9
    @0
    @4
    @12
    @0
    @3
    cn
    wcel
    #
    @4
    @12
    wo
    @0
    cA
    cW
    cword
    #
    c0
    csn
    #
    cdif
    wcel
    #
    @13
    @0
    @16
    cc0
    cA
    cfv
    #
    cD
    wcel
    #
    va
    cv
    #
    cA
    cfv
    @19
    c1
    cmin
    co
    cA
    cfv
    cT
    cfv
    crn
    wcel
    va
    c1
    @3
    cfzo
    co
    wral
    #
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
    va
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
    #
    simp1bi
    #
    @16
    cA
    @14
    wcel
    #
    cA
    c0
    wne
    wa
    @13
    cA
    @14
    c0
    eldifsn
    cW
    cA
    lennncl
    sylbi
    syl
    @3
    elnn1uz2
    sylib
    ord
    @0
    @12
    @9
    @0
    @12
    wa
    #
    @1
    va
    cW
    @19
    cT
    cfv
    #
    crn
    #
    ciun
    #
    @8
    @24
    @3
    c1
    cmin
    co
    #
    c1
    cmin
    co
    #
    cA
    cfv
    #
    cW
    wcel
    @1
    @30
    cT
    cfv
    #
    crn
    #
    wcel
    #
    @1
    @27
    wcel
    @24
    cc0
    @3
    cfzo
    co
    #
    cW
    @29
    cA
    @24
    @23
    @34
    cW
    cA
    wf
    @0
    @23
    @12
    @0
    cA
    @14
    @15
    @22
    eldifad
    adantr
    cW
    cA
    wrdf
    syl
    @24
    @29
    cc0
    @28
    cfz
    co
    #
    @34
    @24
    cc0
    cc0
    @28
    cfzo
    co
    #
    wcel
    #
    @29
    @36
    wcel
    @29
    @35
    wcel
    @24
    @28
    cn
    wcel
    #
    @37
    @24
    @28
    c1
    cuz
    cfv
    #
    cn
    @24
    c1
    cz
    wcel
    @3
    c1
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @28
    @39
    wcel
    1z
    @24
    @3
    @11
    @41
    @0
    @12
    simpr
    c2
    @40
    cuz
    df-2
    fveq2i
    syl6eleq
    c1
    @3
    eluzp1m1
    sylancr
    nnuz
    syl6eleqr
    @28
    lbfzo0
    sylibr
    cc0
    @28
    fzoend
    @29
    cc0
    @28
    elfzofz
    3syl
    @24
    @3
    cz
    wcel
    #
    @34
    @35
    wceq
    @12
    @42
    @0
    c2
    @3
    eluzelz
    adantl
    cc0
    @3
    fzoval
    syl
    eleqtrrd
    ffvelrnd
    @12
    @0
    @38
    @33
    @3
    uz2m1nn
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
    efgsdmi
    sylan2
    va
    @30
    @26
    @32
    cW
    @1
    @19
    @30
    wceq
    @25
    @31
    @19
    @30
    cT
    fveq2
    rneqd
    eliuni
    syl2anc
    va
    vx
    cW
    @26
    @7
    va
    vx
    weq
    @25
    @6
    @19
    @5
    cT
    fveq2
    rneqd
    cbviunv
    syl6eleq
    ex
    syld
    con1d
    syl5
    @0
    @4
    @28
    cA
    cfv
    #
    cD
    wcel
    #
    @2
    @0
    @44
    @4
    @18
    @0
    @16
    @18
    @20
    @21
    simp2bi
    @4
    @43
    @17
    cD
    @4
    @28
    cc0
    cA
    @4
    @28
    c1
    c1
    cmin
    co
    cc0
    @3
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    fveq2d
    eleq1d
    syl5ibrcom
    @0
    @1
    @43
    cD
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
    eleq1d
    sylibrd
    impbid
end
