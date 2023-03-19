include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "cfv.mm"
include "cdm.mm"
include "wfo.mm"
include "efgsfo.mm"
include "foelrn.mm"
include "mpan.mm"
include "cc0.mm"
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
include "efgsdm.mm"
include "simp2bi.mm"
include "adantl.mm"
include "efgsrel.mm"
include "breq1.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "breq2.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "wer.mm"
include "efger.mm"
include "a1i.mm"
include "simprl.mm"
include "simprr.mm"
include "ertr4d.mm"
include "ccnv.mm"
include "cima.mm"
include "efgrelex.mm"
include "wfn.mm"
include "wb.mm"
include "fofn.mm"
include "fniniseg.mm"
include "mp2b.mm"
include "simplbi.mm"
include "ad2antrl.mm"
include "efgsval.mm"
include "syl.mm"
include "simprbi.mm"
include "simpllr.mm"
include "simpld.mm"
include "eqeltrd.mm"
include "efgs1b.mm"
include "mpbid.mm"
include "oveq1d.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "3eqtr3rd.mm"
include "ad2antll.mm"
include "simprd.mm"
include "eqeq12d.mm"
include "biimpd.mm"
include "rexlimdvva.mm"
include "syl5.mm"
include "ex.mm"
include "ralrimivva.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem efgredeu
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
  let vd: setvar d
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
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

  disjoint A d
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
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d t
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint W d
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
  disjoint .~ d
  disjoint .~ m
  disjoint .~ t
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint S d
  disjoint I m
  disjoint I n
  disjoint I t
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint D d
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
  disjoint d o
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
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint D r
  disjoint D s
  disjoint D u
  assert |- ( A e. W -> E! d e. D d .~ A )

  proof
    cA
    cW
    wcel
    #
    vd
    cv
    #
    cA
    c.sm
    wbr
    #
    vd
    cD
    wrex
    #
    @2
    vc
    cv
    #
    cA
    c.sm
    wbr
    #
    wa
    #
    @1
    @4
    wceq
    #
    wi
    #
    vc
    cD
    wral
    vd
    cD
    wral
    @2
    vd
    cD
    wreu
    @0
    cA
    va
    cv
    #
    cS
    cfv
    #
    wceq
    #
    va
    cS
    cdm
    #
    wrex
    #
    @3
    @12
    cW
    cS
    wfo
    #
    @0
    @13
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
    #
    va
    @12
    cW
    cA
    cS
    foelrn
    mpan
    @0
    @11
    @3
    va
    @12
    @0
    @9
    @12
    wcel
    #
    wa
    #
    @3
    @11
    @1
    @10
    c.sm
    wbr
    #
    vd
    cD
    wrex
    #
    @17
    cc0
    @9
    cfv
    #
    cD
    wcel
    #
    @20
    @10
    c.sm
    wbr
    #
    @19
    @16
    @21
    @0
    @16
    @9
    cW
    cword
    c0
    csn
    cdif
    wcel
    @21
    vi
    cv
    #
    @9
    cfv
    @23
    c1
    cmin
    co
    @9
    cfv
    cT
    cfv
    crn
    wcel
    vi
    c1
    @9
    chash
    cfv
    #
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
    @9
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
    adantl
    @16
    @22
    @0
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
    @9
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
    adantl
    @18
    @22
    vd
    @20
    cD
    @1
    @20
    @10
    c.sm
    breq1
    rspcev
    syl2anc
    @11
    @2
    @18
    vd
    cD
    cA
    @10
    @1
    c.sm
    breq2
    rexbidv
    syl5ibrcom
    rexlimdva
    mpd
    @0
    @8
    vd
    vc
    cD
    cD
    @0
    @1
    cD
    wcel
    #
    @4
    cD
    wcel
    #
    wa
    #
    wa
    #
    @6
    @7
    @28
    @6
    wa
    #
    @1
    @4
    c.sm
    wbr
    #
    @7
    @29
    @1
    cA
    @4
    c.sm
    cW
    cW
    c.sm
    wer
    @29
    c.sm
    cI
    cW
    efgval.w
    efgval.r
    efger
    a1i
    @28
    @2
    @5
    simprl
    @28
    @2
    @5
    simprr
    ertr4d
    @30
    @20
    cc0
    vb
    cv
    #
    cfv
    #
    wceq
    #
    vb
    cS
    ccnv
    #
    @4
    csn
    cima
    #
    wrex
    va
    @34
    @1
    csn
    cima
    #
    wrex
    @29
    @7
    vx
    vy
    vz
    vw
    vv
    vt
    @1
    @4
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
    va
    vb
    efgval.w
    efgval.r
    efgval2.m
    efgval2.t
    efgred.d
    efgred.s
    efgrelex
    @29
    @33
    @7
    va
    vb
    @36
    @35
    @29
    @9
    @36
    wcel
    #
    @31
    @35
    wcel
    #
    wa
    #
    wa
    #
    @33
    @7
    @40
    @20
    @1
    @32
    @4
    @40
    @10
    @24
    c1
    cmin
    co
    #
    @9
    cfv
    #
    @1
    @20
    @40
    @16
    @10
    @42
    wceq
    @37
    @16
    @29
    @38
    @37
    @16
    @10
    @1
    wceq
    #
    @14
    cS
    @12
    wfn
    #
    @37
    @16
    @43
    wa
    wb
    @15
    @12
    cW
    cS
    fofn
    #
    @12
    @1
    @9
    cS
    fniniseg
    mp2b
    #
    simplbi
    ad2antrl
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
    vk
    vm
    vn
    @9
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
    @37
    @43
    @29
    @38
    @37
    @16
    @43
    @46
    simprbi
    ad2antrl
    #
    @40
    @41
    cc0
    @9
    @40
    @41
    c1
    c1
    cmin
    co
    #
    cc0
    @40
    @24
    c1
    c1
    cmin
    @40
    @10
    cD
    wcel
    #
    @24
    c1
    wceq
    #
    @40
    @10
    @1
    cD
    @48
    @40
    @25
    @26
    @0
    @27
    @6
    @39
    simpllr
    #
    simpld
    eqeltrd
    @40
    @16
    @50
    @51
    wb
    @47
    vx
    vy
    vz
    vw
    vv
    vt
    @9
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
    mpbid
    oveq1d
    1m1e0
    syl6eq
    fveq2d
    3eqtr3rd
    @40
    @31
    cS
    cfv
    #
    @31
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @31
    cfv
    #
    @4
    @32
    @40
    @31
    @12
    wcel
    #
    @53
    @56
    wceq
    @38
    @57
    @29
    @37
    @38
    @57
    @53
    @4
    wceq
    #
    @14
    @44
    @38
    @57
    @58
    wa
    wb
    @15
    @45
    @12
    @4
    @31
    cS
    fniniseg
    mp2b
    #
    simplbi
    ad2antll
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
    vk
    vm
    vn
    @31
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
    @38
    @58
    @29
    @37
    @38
    @57
    @58
    @59
    simprbi
    ad2antll
    #
    @40
    @55
    cc0
    @31
    @40
    @55
    @49
    cc0
    @40
    @54
    c1
    c1
    cmin
    @40
    @53
    cD
    wcel
    #
    @54
    c1
    wceq
    #
    @40
    @53
    @4
    cD
    @61
    @40
    @25
    @26
    @52
    simprd
    eqeltrd
    @40
    @57
    @62
    @63
    wb
    @60
    vx
    vy
    vz
    vw
    vv
    vt
    @31
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
    mpbid
    oveq1d
    1m1e0
    syl6eq
    fveq2d
    3eqtr3rd
    eqeq12d
    biimpd
    rexlimdvva
    syl5
    mpd
    ex
    ralrimivva
    @2
    @5
    vd
    vc
    cD
    @1
    @4
    cA
    c.sm
    breq1
    reu4
    sylanbrc
end
