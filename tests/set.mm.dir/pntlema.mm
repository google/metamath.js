include "c4.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "caddc.mm"
include "c2.mm"
include "cexp.mm"
include "c3.mm"
include "cdc.mm"
include "cmin.mm"
include "ce.mm"
include "cfv.mm"
include "crp.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "simpld.mm"
include "cn.mm"
include "4nn.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "pntlemd.mm"
include "simp1d.mm"
include "cc0.mm"
include "cioo.mm"
include "clt.mm"
include "w3a.mm"
include "pntlemc.mm"
include "rpmulcld.mm"
include "rpdivcl.mm"
include "sylancr.mm"
include "rpaddcld.mm"
include "2z.mm"
include "rpexpcl.mm"
include "sylancl.mm"
include "simp2d.mm"
include "4z.mm"
include "3nn0.mm"
include "2nn.mm"
include "decnncl.mm"
include "rpmulcl.mm"
include "simp3d.mm"
include "rpdivcld.mm"
include "3nn.mm"
include "rpred.mm"
include "rpefcld.mm"
include "syl5eqel.mm"

theorem pntlema
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cU: class U
  let cE: class E
  let cF: class F
  let cK: class K
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cI: class I
  let vn: setvar n
  let vy: setvar y
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vu: setvar u
  let cM: class M
  let cO: class O
  let vv: setvar v
  let cN: class N
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vl: setvar l
  let cV: class V
  let cZ: class Z
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
  assert |- ( ph -> W e. RR+ )

  proof
    wph
    cW
    cY
    c4
    cL
    cE
    cmul
    co
    #
    cdiv
    co
    #
    caddc
    co
    #
    c2
    cexp
    co
    #
    cX
    cK
    c2
    cexp
    co
    #
    cmul
    co
    #
    c4
    cexp
    co
    #
    c3
    c2
    cdc
    #
    cB
    cmul
    co
    #
    cU
    cE
    cmin
    co
    #
    cL
    cE
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    cU
    c3
    cmul
    co
    #
    cC
    caddc
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    caddc
    co
    #
    caddc
    co
    crp
    pntlem1.w
    wph
    @3
    @18
    wph
    @2
    crp
    wcel
    c2
    cz
    wcel
    #
    @3
    crp
    wcel
    wph
    cY
    @1
    wph
    cY
    crp
    wcel
    c1
    cY
    cle
    wbr
    pntlem1.y
    simpld
    wph
    c4
    crp
    wcel
    #
    @0
    crp
    wcel
    @1
    crp
    wcel
    c4
    cn
    wcel
    @20
    4nn
    c4
    nnrp
    ax-mp
    wph
    cL
    cE
    wph
    cL
    crp
    wcel
    cD
    crp
    wcel
    cF
    crp
    wcel
    wph
    cA
    cB
    cD
    cR
    cF
    cL
    va
    pntlem1.r
    pntlem1.a
    pntlem1.b
    pntlem1.l
    pntlem1.d
    pntlem1.f
    pntlemd
    simp1d
    #
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
    @9
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
    simp1d
    #
    rpmulcld
    c4
    @0
    rpdivcl
    sylancr
    rpaddcld
    2z
    @2
    c2
    rpexpcl
    sylancl
    wph
    @6
    @17
    wph
    @5
    crp
    wcel
    c4
    cz
    wcel
    @6
    crp
    wcel
    wph
    cX
    @4
    wph
    cX
    crp
    wcel
    cY
    cX
    clt
    wbr
    pntlem1.x
    simpld
    wph
    @23
    @19
    @4
    crp
    wcel
    wph
    @22
    @23
    @27
    @28
    simp2d
    2z
    cK
    c2
    rpexpcl
    sylancl
    rpmulcld
    4z
    @5
    c4
    rpexpcl
    sylancl
    wph
    @16
    wph
    @16
    wph
    @13
    @15
    wph
    @8
    @12
    wph
    @7
    crp
    wcel
    #
    cB
    crp
    wcel
    @8
    crp
    wcel
    @7
    cn
    wcel
    @30
    c3
    c2
    3nn0
    2nn
    decnncl
    @7
    nnrp
    ax-mp
    pntlem1.b
    @7
    cB
    rpmulcl
    sylancr
    wph
    @9
    @11
    wph
    @24
    @25
    @26
    wph
    @22
    @23
    @27
    @28
    simp3d
    simp3d
    wph
    cL
    @10
    @21
    wph
    @22
    @19
    @10
    crp
    wcel
    @29
    2z
    cE
    c2
    rpexpcl
    sylancl
    rpmulcld
    rpmulcld
    rpdivcld
    wph
    @14
    cC
    wph
    cU
    crp
    wcel
    c3
    crp
    wcel
    #
    @14
    crp
    wcel
    pntlem1.u
    c3
    cn
    wcel
    @31
    3nn
    c3
    nnrp
    ax-mp
    cU
    c3
    rpmulcl
    sylancl
    pntlem1.c
    rpaddcld
    rpmulcld
    rpred
    rpefcld
    rpaddcld
    rpaddcld
    syl5eqel
end
