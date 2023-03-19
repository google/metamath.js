include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cexp.mm"
include "clt.mm"
include "wbr.mm"
include "csqrt.mm"
include "cfv.mm"
include "cle.mm"
include "clog.mm"
include "cmul.mm"
include "cdiv.mm"
include "crp.mm"
include "simpld.mm"
include "adantr.mm"
include "relogcld.mm"
include "cc0.mm"
include "c1.mm"
include "cioo.mm"
include "cmin.mm"
include "w3a.mm"
include "pntlemc.mm"
include "simp2d.mm"
include "rpred.mm"
include "simp3d.mm"
include "rplogcld.mm"
include "rerpdivcld.mm"
include "cn.mm"
include "cuz.mm"
include "c4.mm"
include "pntlemg.mm"
include "simp1d.mm"
include "nnred.mm"
include "elfzuz.mm"
include "eluznn.mm"
include "syl2an.mm"
include "cfl.mm"
include "caddc.mm"
include "cr.mm"
include "flltp1.mm"
include "syl.mm"
include "syl6breqr.mm"
include "elfzle1.mm"
include "adantl.mm"
include "ltletrd.mm"
include "ltdivmul2d.mm"
include "mpbid.mm"
include "cz.mm"
include "wceq.mm"
include "elfzelz.mm"
include "relogexp.mm"
include "syl2anc.mm"
include "breqtrrd.mm"
include "wb.mm"
include "rpexpcld.mm"
include "logltb.mm"
include "mpbird.mm"
include "c2.mm"
include "oveq2d.mm"
include "2z.mm"
include "sylancl.mm"
include "2cnd.mm"
include "recnd.mm"
include "mulassd.mm"
include "3eqtr4d.mm"
include "elfzle2.mm"
include "syl6breq.mm"
include "ceu.mm"
include "c3.mm"
include "cdc.mm"
include "pntlemb.mm"
include "rehalfcld.mm"
include "flge.mm"
include "2re.mm"
include "a1i.mm"
include "2pos.mm"
include "lemuldiv2.mm"
include "syl112anc.mm"
include "remulcl.mm"
include "sylancr.mm"
include "lemuldivd.mm"
include "eqbrtrd.mm"
include "rpexpcl.mm"
include "logled.mm"
include "rprege0d.mm"
include "resqrtth.mm"
include "rpsqrtcld.mm"
include "le2sq.mm"
include "jca.mm"

theorem pntlemh
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cU: class U
  let cE: class E
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cI: class I
  let vn: setvar n
  let vy: setvar y
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vu: setvar u
  let cO: class O
  let vv: setvar v
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vl: setvar l
  let cV: class V
  assume pntlem1.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntlem1.a: |- ( ph -> A e. RR+ )
  assume pntlem1.b: |- ( ph -> B e. RR+ )
  assume pntlem1.l: |- ( ph -> L e. ( 0 (,) 1 ) )
  assume pntlem1.d: |- D = ( A + 1 )
  assume pntlem1.f: |- F = ( ( 1 - ( 1 / D ) ) x. ( ( L / ( ; 3 2 x. B ) ) / ( D ^ 2 ) ) )
  assume pntlem1.u: |- ( ph -> U e. RR+ )
  assume pntlem1.u2: |- ( ph -> U <_ A )
  assume pntlem1.e: |- E = ( U / D )
  assume pntlem1.k: |- K = ( exp ` ( B / E ) )
  assume pntlem1.y: |- ( ph -> ( Y e. RR+ /\ 1 <_ Y ) )
  assume pntlem1.x: |- ( ph -> ( X e. RR+ /\ Y < X ) )
  assume pntlem1.c: |- ( ph -> C e. RR+ )
  assume pntlem1.w: |- W = ( ( ( Y + ( 4 / ( L x. E ) ) ) ^ 2 ) + ( ( ( X x. ( K ^ 2 ) ) ^ 4 ) + ( exp ` ( ( ( ; 3 2 x. B ) / ( ( U - E ) x. ( L x. ( E ^ 2 ) ) ) ) x. ( ( U x. 3 ) + C ) ) ) ) )
  assume pntlem1.z: |- ( ph -> Z e. ( W [,) +oo ) )
  assume pntlem1.m: |- M = ( ( |_ ` ( ( log ` X ) / ( log ` K ) ) ) + 1 )
  assume pntlem1.n: |- N = ( |_ ` ( ( ( log ` Z ) / ( log ` K ) ) / 2 ) )

  disjoint E a
  disjoint x z
  disjoint C x
  disjoint C z
  disjoint F w
  disjoint I n
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint J n
  disjoint x y
  disjoint J x
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint L j
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint L k
  disjoint m n
  disjoint m u
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint L m
  disjoint n u
  disjoint L n
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint L u
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M z
  disjoint O n
  disjoint O x
  disjoint O z
  disjoint j v
  disjoint j ph
  disjoint m v
  disjoint m ph
  disjoint n v
  disjoint n ph
  disjoint v x
  disjoint ph v
  disjoint ph x
  disjoint N j
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N z
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b l
  disjoint b m
  disjoint b n
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint R b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c l
  disjoint c m
  disjoint c n
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d l
  disjoint d m
  disjoint d n
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint R d
  disjoint e f
  disjoint e g
  disjoint e i
  disjoint e j
  disjoint e k
  disjoint e l
  disjoint e m
  disjoint e n
  disjoint e u
  disjoint e v
  disjoint e w
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint R e
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f l
  disjoint f m
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint R f
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g l
  disjoint g m
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint R g
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i n
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint R i
  disjoint j l
  disjoint j w
  disjoint R j
  disjoint k l
  disjoint k v
  disjoint k w
  disjoint R k
  disjoint l m
  disjoint l n
  disjoint l u
  disjoint l v
  disjoint l w
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint R l
  disjoint m w
  disjoint R m
  disjoint n w
  disjoint R n
  disjoint u v
  disjoint u w
  disjoint R u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint R v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint V n
  disjoint V u
  disjoint U j
  disjoint U m
  disjoint U n
  disjoint U w
  disjoint U x
  disjoint U z
  disjoint W n
  disjoint W v
  disjoint W w
  disjoint W z
  disjoint X k
  disjoint X n
  disjoint X y
  disjoint X z
  disjoint Y i
  disjoint Y j
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint Y z
  disjoint a e
  disjoint a g
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint E e
  disjoint E g
  disjoint E j
  disjoint E k
  disjoint E m
  disjoint E n
  disjoint E u
  disjoint E v
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint Z j
  disjoint Z m
  disjoint Z n
  disjoint Z u
  disjoint Z x
  disjoint Z z
  assert |- ( ( ph /\ J e. ( M ... N ) ) -> ( X < ( K ^ J ) /\ ( K ^ J ) <_ ( sqrt ` Z ) ) )

  proof
    wph
    cJ
    cM
    cN
    cfz
    co
    wcel
    #
    wa
    #
    cX
    cK
    cJ
    cexp
    co
    #
    clt
    wbr
    #
    @2
    cZ
    csqrt
    cfv
    #
    cle
    wbr
    #
    @1
    @3
    cX
    clog
    cfv
    #
    @2
    clog
    cfv
    #
    clt
    wbr
    #
    @1
    @6
    cJ
    cK
    clog
    cfv
    #
    cmul
    co
    #
    @7
    clt
    @1
    @6
    @9
    cdiv
    co
    #
    cJ
    clt
    wbr
    @6
    @10
    clt
    wbr
    @1
    @11
    cM
    cJ
    @1
    @6
    @9
    @1
    cX
    wph
    cX
    crp
    wcel
    #
    @0
    wph
    @12
    cY
    cX
    clt
    wbr
    pntlem1.x
    simpld
    adantr
    #
    relogcld
    #
    wph
    @9
    crp
    wcel
    @0
    wph
    cK
    wph
    cK
    wph
    cE
    crp
    wcel
    #
    cK
    crp
    wcel
    #
    cE
    cc0
    c1
    cioo
    co
    wcel
    #
    c1
    cK
    clt
    wbr
    #
    cU
    cE
    cmin
    co
    #
    crp
    wcel
    #
    w3a
    #
    wph
    cA
    cB
    cD
    cR
    cU
    cE
    cF
    cK
    cL
    va
    pntlem1.r
    pntlem1.a
    pntlem1.b
    pntlem1.l
    pntlem1.d
    pntlem1.f
    pntlem1.u
    pntlem1.u2
    pntlem1.e
    pntlem1.k
    pntlemc
    #
    simp2d
    #
    rpred
    wph
    @17
    @18
    @20
    wph
    @15
    @16
    @21
    @22
    simp3d
    simp2d
    rplogcld
    adantr
    #
    rerpdivcld
    #
    @1
    cM
    wph
    cM
    cn
    wcel
    #
    @0
    wph
    @26
    cN
    cM
    cuz
    cfv
    #
    wcel
    cZ
    clog
    cfv
    #
    @9
    cdiv
    co
    #
    c4
    cdiv
    co
    #
    cN
    cM
    cmin
    co
    cle
    wbr
    wph
    cA
    cB
    cC
    cD
    cR
    cU
    cE
    cF
    cK
    cL
    cM
    cN
    cW
    cX
    cY
    cZ
    va
    pntlem1.r
    pntlem1.a
    pntlem1.b
    pntlem1.l
    pntlem1.d
    pntlem1.f
    pntlem1.u
    pntlem1.u2
    pntlem1.e
    pntlem1.k
    pntlem1.y
    pntlem1.x
    pntlem1.c
    pntlem1.w
    pntlem1.z
    pntlem1.m
    pntlem1.n
    pntlemg
    simp1d
    #
    adantr
    nnred
    @1
    cJ
    wph
    @26
    cJ
    @27
    wcel
    cJ
    cn
    wcel
    @0
    @31
    cJ
    cM
    cN
    elfzuz
    cJ
    cM
    eluznn
    syl2an
    nnred
    #
    @1
    @11
    @11
    cfl
    cfv
    c1
    caddc
    co
    #
    cM
    clt
    @1
    @11
    cr
    wcel
    @11
    @33
    clt
    wbr
    @25
    @11
    flltp1
    syl
    pntlem1.m
    syl6breqr
    @0
    cM
    cJ
    cle
    wbr
    wph
    cJ
    cM
    cN
    elfzle1
    adantl
    ltletrd
    @1
    @6
    cJ
    @9
    @14
    @32
    @24
    ltdivmul2d
    mpbid
    @1
    @16
    cJ
    cz
    wcel
    #
    @7
    @10
    wceq
    wph
    @16
    @0
    @23
    adantr
    #
    @0
    @34
    wph
    cJ
    cM
    cN
    elfzelz
    adantl
    #
    cK
    cJ
    relogexp
    syl2anc
    #
    breqtrrd
    @1
    @12
    @2
    crp
    wcel
    #
    @3
    @8
    wb
    @13
    @1
    cK
    cJ
    @35
    @36
    rpexpcld
    #
    cX
    @2
    logltb
    syl2anc
    mpbird
    @1
    @5
    @2
    c2
    cexp
    co
    #
    @4
    c2
    cexp
    co
    #
    cle
    wbr
    #
    @1
    @40
    cZ
    @41
    cle
    @1
    @40
    cZ
    cle
    wbr
    @40
    clog
    cfv
    #
    @28
    cle
    wbr
    @1
    @43
    c2
    cJ
    cmul
    co
    #
    @9
    cmul
    co
    #
    @28
    cle
    @1
    c2
    @7
    cmul
    co
    #
    c2
    @10
    cmul
    co
    @43
    @45
    @1
    @7
    @10
    c2
    cmul
    @37
    oveq2d
    @1
    @38
    c2
    cz
    wcel
    #
    @43
    @46
    wceq
    @39
    2z
    @2
    c2
    relogexp
    sylancl
    @1
    c2
    cJ
    @9
    @1
    2cnd
    @1
    cJ
    @32
    recnd
    @1
    @9
    @1
    cK
    @35
    relogcld
    recnd
    mulassd
    3eqtr4d
    @1
    @45
    @28
    cle
    wbr
    @44
    @29
    cle
    wbr
    #
    @1
    @48
    cJ
    @29
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    @1
    @50
    cJ
    @49
    cfl
    cfv
    #
    cle
    wbr
    #
    @1
    cJ
    cN
    @51
    cle
    @0
    cJ
    cN
    cle
    wbr
    wph
    cJ
    cM
    cN
    elfzle2
    adantl
    pntlem1.n
    syl6breq
    @1
    @49
    cr
    wcel
    @34
    @50
    @52
    wb
    @1
    @29
    @1
    @28
    @9
    @1
    cZ
    wph
    cZ
    crp
    wcel
    #
    @0
    wph
    @53
    c1
    cZ
    clt
    wbr
    ceu
    @4
    cle
    wbr
    @4
    cZ
    cY
    cdiv
    co
    cle
    wbr
    w3a
    c4
    cL
    cE
    cmul
    co
    cdiv
    co
    @4
    cle
    wbr
    @11
    c2
    caddc
    co
    @30
    cle
    wbr
    cU
    c3
    cmul
    co
    cC
    caddc
    co
    @19
    cL
    cE
    c2
    cexp
    co
    cmul
    co
    c3
    c2
    cdc
    cB
    cmul
    co
    cdiv
    co
    cmul
    co
    @28
    cmul
    co
    cle
    wbr
    w3a
    wph
    cA
    cB
    cC
    cD
    cR
    cU
    cE
    cF
    cK
    cL
    cW
    cX
    cY
    cZ
    va
    pntlem1.r
    pntlem1.a
    pntlem1.b
    pntlem1.l
    pntlem1.d
    pntlem1.f
    pntlem1.u
    pntlem1.u2
    pntlem1.e
    pntlem1.k
    pntlem1.y
    pntlem1.x
    pntlem1.c
    pntlem1.w
    pntlem1.z
    pntlemb
    simp1d
    adantr
    #
    relogcld
    #
    @24
    rerpdivcld
    #
    rehalfcld
    @36
    @49
    cJ
    flge
    syl2anc
    mpbird
    @1
    cJ
    cr
    wcel
    #
    @29
    cr
    wcel
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @48
    @50
    wb
    @32
    @56
    @58
    @1
    2re
    a1i
    @59
    @1
    2pos
    a1i
    cJ
    @29
    c2
    lemuldiv2
    syl112anc
    mpbird
    @1
    @44
    @28
    @9
    @1
    @58
    @57
    @44
    cr
    wcel
    2re
    @32
    c2
    cJ
    remulcl
    sylancr
    @55
    @24
    lemuldivd
    mpbird
    eqbrtrd
    @1
    @40
    cZ
    @1
    @38
    @47
    @40
    crp
    wcel
    @39
    2z
    @2
    c2
    rpexpcl
    sylancl
    @54
    logled
    mpbird
    @1
    cZ
    cr
    wcel
    cc0
    cZ
    cle
    wbr
    wa
    @41
    cZ
    wceq
    @1
    cZ
    @54
    rprege0d
    cZ
    resqrtth
    syl
    breqtrrd
    @1
    @2
    cr
    wcel
    cc0
    @2
    cle
    wbr
    wa
    @4
    cr
    wcel
    cc0
    @4
    cle
    wbr
    wa
    @5
    @42
    wb
    @1
    @2
    @39
    rprege0d
    @1
    @4
    @1
    cZ
    @54
    rpsqrtcld
    rprege0d
    @2
    @4
    le2sq
    syl2anc
    mpbird
    jca
end
