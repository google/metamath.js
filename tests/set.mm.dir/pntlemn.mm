include "cn.mm"
include "wcel.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cfv.mm"
include "cabs.mm"
include "cmin.mm"
include "clog.mm"
include "crp.mm"
include "adantr.mm"
include "rpred.mm"
include "simprl.mm"
include "nndivred.mm"
include "cr.mm"
include "c1.mm"
include "clt.mm"
include "ceu.mm"
include "csqrt.mm"
include "w3a.mm"
include "c4.mm"
include "cmul.mm"
include "c2.mm"
include "caddc.mm"
include "c3.mm"
include "cexp.mm"
include "cdc.mm"
include "pntlemb.mm"
include "simp1d.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "pntrf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "rerpdivcld.mm"
include "recnd.mm"
include "abscld.mm"
include "resubcld.mm"
include "relogcld.mm"
include "cc0.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "rpcnne0d.mm"
include "divdiv2.mm"
include "syl3anc.mm"
include "nncnd.mm"
include "div23.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "absmuld.mm"
include "rprege0d.mm"
include "absid.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "cpnf.mm"
include "cico.mm"
include "cv.mm"
include "wral.mm"
include "simprr.mm"
include "simpld.mm"
include "lemuldiv2d.mm"
include "mpbird.mm"
include "lemuldivd.mm"
include "mpbid.mm"
include "wb.mm"
include "elicopnf.mm"
include "mpbir2and.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqbrtrrd.mm"
include "subge0d.mm"
include "log1.mm"
include "nnge1.mm"
include "ad2antrl.mm"
include "1rp.mm"
include "logleb.mm"
include "sylancr.mm"
include "syl5eqbrr.mm"
include "mulge0d.mm"

theorem pntlemn
  let wph: wff ph
  let vz: setvar z
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
  assume pntlem1.U: |- ( ph -> A. z e. ( Y [,) +oo ) ( abs ` ( ( R ` z ) / z ) ) <_ U )

  disjoint C z
  disjoint J z
  disjoint L z
  disjoint K z
  disjoint M z
  disjoint N z
  disjoint R z
  disjoint U z
  disjoint W z
  disjoint X z
  disjoint Y z
  disjoint a z
  disjoint E a
  disjoint E z
  disjoint Z z
  disjoint x z
  disjoint C x
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
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M x
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
  disjoint V n
  disjoint V u
  disjoint U j
  disjoint U m
  disjoint U n
  disjoint U w
  disjoint U x
  disjoint W n
  disjoint W v
  disjoint W w
  disjoint X k
  disjoint X n
  disjoint X y
  disjoint Y i
  disjoint Y j
  disjoint Y m
  disjoint Y n
  disjoint Y x
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
  disjoint Z j
  disjoint Z m
  disjoint Z n
  disjoint Z u
  disjoint Z x
  assert |- ( ( ph /\ ( J e. NN /\ J <_ ( Z / Y ) ) ) -> 0 <_ ( ( ( U / J ) - ( abs ` ( ( R ` ( Z / J ) ) / Z ) ) ) x. ( log ` J ) ) )

  proof
    wph
    cJ
    cn
    wcel
    #
    cJ
    cZ
    cY
    cdiv
    co
    #
    cle
    wbr
    #
    wa
    #
    wa
    #
    cU
    cJ
    cdiv
    co
    #
    cZ
    cJ
    cdiv
    co
    #
    cR
    cfv
    #
    cZ
    cdiv
    co
    #
    cabs
    cfv
    #
    cmin
    co
    #
    cJ
    clog
    cfv
    #
    @4
    @5
    @9
    @4
    cU
    cJ
    @4
    cU
    wph
    cU
    crp
    wcel
    @3
    pntlem1.u
    adantr
    rpred
    #
    wph
    @0
    @2
    simprl
    #
    nndivred
    #
    @4
    @8
    @4
    @8
    @4
    @7
    cZ
    @4
    @6
    crp
    wcel
    @7
    cr
    wcel
    @4
    cZ
    cJ
    wph
    cZ
    crp
    wcel
    #
    @3
    wph
    @15
    c1
    cZ
    clt
    wbr
    ceu
    cZ
    csqrt
    cfv
    #
    cle
    wbr
    @16
    @1
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
    @16
    cle
    wbr
    cX
    clog
    cfv
    cK
    clog
    cfv
    #
    cdiv
    co
    c2
    caddc
    co
    cZ
    clog
    cfv
    #
    @17
    cdiv
    co
    c4
    cdiv
    co
    cle
    wbr
    cU
    c3
    cmul
    co
    cC
    caddc
    co
    cU
    cE
    cmin
    co
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
    @18
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
    @4
    cJ
    @13
    nnrpd
    #
    rpdivcld
    #
    crp
    cr
    @6
    cR
    cR
    va
    pntlem1.r
    pntrf
    ffvelrni
    syl
    #
    @19
    rerpdivcld
    recnd
    #
    abscld
    #
    resubcld
    @4
    cJ
    @20
    relogcld
    @4
    cc0
    @10
    cle
    wbr
    @9
    @5
    cle
    wbr
    #
    @4
    @9
    cJ
    cmul
    co
    #
    cU
    cle
    wbr
    @25
    @4
    @7
    @6
    cdiv
    co
    #
    cabs
    cfv
    #
    @26
    cU
    cle
    @4
    @28
    @8
    cJ
    cmul
    co
    #
    cabs
    cfv
    @9
    cJ
    cabs
    cfv
    #
    cmul
    co
    @26
    @4
    @27
    @29
    cabs
    @4
    @27
    @7
    cJ
    cmul
    co
    cZ
    cdiv
    co
    #
    @29
    @4
    @7
    cc
    wcel
    #
    cZ
    cc
    wcel
    cZ
    cc0
    wne
    wa
    #
    cJ
    cc
    wcel
    #
    cJ
    cc0
    wne
    wa
    @27
    @31
    wceq
    @4
    @7
    @22
    recnd
    #
    @4
    cZ
    @19
    rpcnne0d
    #
    @4
    cJ
    @20
    rpcnne0d
    @7
    cZ
    cJ
    divdiv2
    syl3anc
    @4
    @32
    @34
    @33
    @31
    @29
    wceq
    @35
    @4
    cJ
    @13
    nncnd
    #
    @36
    @7
    cJ
    cZ
    div23
    syl3anc
    eqtrd
    fveq2d
    @4
    @8
    cJ
    @23
    @37
    absmuld
    @4
    @30
    cJ
    @9
    cmul
    @4
    cJ
    cr
    wcel
    cc0
    cJ
    cle
    wbr
    wa
    @30
    cJ
    wceq
    @4
    cJ
    @20
    rprege0d
    cJ
    absid
    syl
    oveq2d
    3eqtrd
    @4
    @6
    cY
    cpnf
    cico
    co
    #
    wcel
    #
    vz
    cv
    #
    cR
    cfv
    #
    @40
    cdiv
    co
    #
    cabs
    cfv
    #
    cU
    cle
    wbr
    #
    vz
    @38
    wral
    #
    @28
    cU
    cle
    wbr
    #
    @4
    @39
    @6
    cr
    wcel
    #
    cY
    @6
    cle
    wbr
    #
    @4
    @6
    @21
    rpred
    @4
    cY
    cJ
    cmul
    co
    cZ
    cle
    wbr
    #
    @48
    @4
    @49
    @2
    wph
    @0
    @2
    simprr
    @4
    cJ
    cZ
    cY
    @4
    cJ
    @20
    rpred
    @4
    cZ
    @19
    rpred
    #
    wph
    cY
    crp
    wcel
    #
    @3
    wph
    @51
    c1
    cY
    cle
    wbr
    pntlem1.y
    simpld
    adantr
    #
    lemuldiv2d
    mpbird
    @4
    cY
    cZ
    cJ
    @4
    cY
    @52
    rpred
    #
    @50
    @20
    lemuldivd
    mpbid
    @4
    cY
    cr
    wcel
    @39
    @47
    @48
    wa
    wb
    @53
    cY
    @6
    elicopnf
    syl
    mpbir2and
    wph
    @45
    @3
    pntlem1.U
    adantr
    @44
    @46
    vz
    @6
    @38
    @40
    @6
    wceq
    #
    @43
    @28
    cU
    cle
    @54
    @42
    @27
    cabs
    @54
    @41
    @7
    @40
    @6
    cdiv
    @40
    @6
    cR
    fveq2
    @54
    id
    oveq12d
    fveq2d
    breq1d
    rspcv
    sylc
    eqbrtrrd
    @4
    @9
    cU
    cJ
    @24
    @12
    @20
    lemuldivd
    mpbid
    @4
    @5
    @9
    @14
    @24
    subge0d
    mpbird
    @4
    cc0
    c1
    clog
    cfv
    #
    @11
    cle
    log1
    @4
    c1
    cJ
    cle
    wbr
    #
    @55
    @11
    cle
    wbr
    #
    @0
    @56
    wph
    @2
    cJ
    nnge1
    ad2antrl
    @4
    c1
    crp
    wcel
    cJ
    crp
    wcel
    @56
    @57
    wb
    1rp
    @20
    c1
    cJ
    logleb
    sylancr
    mpbid
    syl5eqbrr
    mulge0d
end
