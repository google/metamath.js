include "crp.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cioo.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "w3a.mm"
include "cdiv.mm"
include "pntlemd.mm"
include "simp2d.mm"
include "rpdivcld.mm"
include "syl5eqel.mm"
include "ce.mm"
include "cfv.mm"
include "rpred.mm"
include "rpefcld.mm"
include "cr.mm"
include "rpgt0d.mm"
include "cmul.mm"
include "caddc.mm"
include "ltp1d.mm"
include "syl6breqr.mm"
include "lelttrd.mm"
include "rpcnd.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "1red.mm"
include "ltdivmuld.mm"
include "mpbird.mm"
include "syl5eqbr.mm"
include "cxr.mm"
include "wb.mm"
include "0xr.mm"
include "1re.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "efgt1.mm"
include "syl.mm"
include "ltaddrp.mm"
include "sylancr.mm"
include "cc.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "rpcnne0d.mm"
include "divid.mm"
include "ax-1cn.mm"
include "addcom.mm"
include "sylancl.mm"
include "syl5eq.mm"
include "3brtr4d.mm"
include "ltdiv23d.mm"
include "difrp.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "3jca.mm"

theorem pntlemc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cU: class U
  let cE: class E
  let cF: class F
  let cK: class K
  let cL: class L
  let va: setvar a
  let vx: setvar x
  let vz: setvar z
  let cC: class C
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
  let cW: class W
  let cX: class X
  let cY: class Y
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
  assert |- ( ph -> ( E e. RR+ /\ K e. RR+ /\ ( E e. ( 0 (,) 1 ) /\ 1 < K /\ ( U - E ) e. RR+ ) ) )

  proof
    wph
    cE
    crp
    wcel
    cK
    crp
    wcel
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
    crp
    wcel
    #
    w3a
    wph
    cE
    cU
    cD
    cdiv
    co
    #
    crp
    pntlem1.e
    wph
    cU
    cD
    pntlem1.u
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
    simp2d
    #
    rpdivcld
    syl5eqel
    #
    wph
    cK
    cB
    cE
    cdiv
    co
    #
    ce
    cfv
    #
    crp
    pntlem1.k
    wph
    @6
    wph
    @6
    wph
    cB
    cE
    pntlem1.b
    @5
    rpdivcld
    #
    rpred
    rpefcld
    syl5eqel
    wph
    @0
    @1
    @2
    wph
    cE
    cr
    wcel
    #
    cc0
    cE
    clt
    wbr
    #
    cE
    c1
    clt
    wbr
    #
    @0
    wph
    cE
    @5
    rpred
    #
    wph
    cE
    @5
    rpgt0d
    wph
    cE
    @3
    c1
    clt
    pntlem1.e
    wph
    @3
    c1
    clt
    wbr
    cU
    cD
    c1
    cmul
    co
    #
    clt
    wbr
    wph
    cU
    cD
    @13
    clt
    wph
    cU
    cA
    cD
    wph
    cU
    pntlem1.u
    rpred
    #
    wph
    cA
    pntlem1.a
    rpred
    #
    wph
    cD
    @4
    rpred
    pntlem1.u2
    wph
    cA
    cA
    c1
    caddc
    co
    #
    cD
    clt
    wph
    cA
    @15
    ltp1d
    pntlem1.d
    syl6breqr
    lelttrd
    wph
    cD
    wph
    cD
    @4
    rpcnd
    mulid1d
    breqtrrd
    wph
    cU
    c1
    cD
    @14
    wph
    1red
    @4
    ltdivmuld
    mpbird
    syl5eqbr
    cc0
    cxr
    wcel
    c1
    cxr
    wcel
    @0
    @9
    @10
    @11
    w3a
    wb
    0xr
    c1
    1re
    rexri
    cc0
    c1
    cE
    elioo2
    mp2an
    syl3anbrc
    wph
    c1
    @7
    cK
    clt
    wph
    @6
    crp
    wcel
    c1
    @7
    clt
    wbr
    @8
    @6
    efgt1
    syl
    pntlem1.k
    syl6breqr
    wph
    cE
    cU
    clt
    wbr
    #
    @2
    wph
    cE
    @3
    cU
    clt
    pntlem1.e
    wph
    cU
    cU
    cD
    @14
    pntlem1.u
    @4
    wph
    c1
    c1
    cA
    caddc
    co
    #
    cU
    cU
    cdiv
    co
    #
    cD
    clt
    wph
    c1
    cr
    wcel
    cA
    crp
    wcel
    c1
    @18
    clt
    wbr
    1re
    pntlem1.a
    c1
    cA
    ltaddrp
    sylancr
    wph
    cU
    cc
    wcel
    cU
    cc0
    wne
    wa
    @19
    c1
    wceq
    wph
    cU
    pntlem1.u
    rpcnne0d
    cU
    divid
    syl
    wph
    cD
    @16
    @18
    pntlem1.d
    wph
    cA
    cc
    wcel
    c1
    cc
    wcel
    @16
    @18
    wceq
    wph
    cA
    pntlem1.a
    rpcnd
    ax-1cn
    cA
    c1
    addcom
    sylancl
    syl5eq
    3brtr4d
    ltdiv23d
    syl5eqbr
    wph
    @9
    cU
    cr
    wcel
    @17
    @2
    wb
    @12
    @14
    cE
    cU
    difrp
    syl2anc
    mpbid
    3jca
    3jca
end
