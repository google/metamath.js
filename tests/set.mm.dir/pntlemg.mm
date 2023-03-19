include "cn.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "clog.mm"
include "cdiv.mm"
include "co.mm"
include "c4.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "cr.mm"
include "cc0.mm"
include "wa.mm"
include "cn0.mm"
include "crp.mm"
include "clt.mm"
include "simpld.mm"
include "rpred.mm"
include "1red.mm"
include "simprd.mm"
include "lelttrd.mm"
include "rplogcld.mm"
include "cioo.mm"
include "w3a.mm"
include "pntlemc.mm"
include "simp2d.mm"
include "simp3d.mm"
include "rpdivcld.mm"
include "rprege0d.mm"
include "flge0nn0.mm"
include "nn0p1nn.mm"
include "3syl.mm"
include "syl5eqel.mm"
include "cz.mm"
include "nnzd.mm"
include "c2.mm"
include "ceu.mm"
include "csqrt.mm"
include "cmul.mm"
include "c3.mm"
include "cexp.mm"
include "cdc.mm"
include "pntlemb.mm"
include "simp1d.mm"
include "relogcld.mm"
include "rerpdivcld.mm"
include "rehalfcld.mm"
include "flcld.mm"
include "0red.mm"
include "4nn.mm"
include "nndivre.mm"
include "sylancl.mm"
include "zred.mm"
include "nnred.mm"
include "resubcld.mm"
include "4re.mm"
include "4pos.mm"
include "elrpii.mm"
include "rpdivcl.mm"
include "rpge0d.mm"
include "recnd.mm"
include "nncnd.mm"
include "1cnd.mm"
include "addassd.mm"
include "readdcld.mm"
include "peano2re.mm"
include "syl.mm"
include "2re.mm"
include "a1i.mm"
include "reflcl.mm"
include "oveq1i.mm"
include "df-2.mm"
include "oveq2i.mm"
include "3eqtr4g.mm"
include "flle.mm"
include "leadd1dd.mm"
include "eqbrtrd.mm"
include "letrd.mm"
include "leadd2dd.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "divdiv1d.mm"
include "2t2e4.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "divcan2d.mm"
include "2timesd.mm"
include "3eqtr3d.mm"
include "breqtrrd.mm"
include "fllep1.mm"
include "syl6breqr.mm"
include "leadd1d.mm"
include "mpbird.mm"
include "wb.mm"
include "leaddsub.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "subge0d.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "3jca.mm"

theorem pntlemg
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
  let cJ: class J
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
  assert |- ( ph -> ( M e. NN /\ N e. ( ZZ>= ` M ) /\ ( ( ( log ` Z ) / ( log ` K ) ) / 4 ) <_ ( N - M ) ) )

  proof
    wph
    cM
    cn
    wcel
    cN
    cM
    cuz
    cfv
    wcel
    #
    cZ
    clog
    cfv
    #
    cK
    clog
    cfv
    #
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
    #
    cle
    wbr
    #
    wph
    cM
    cX
    clog
    cfv
    #
    @2
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cn
    pntlem1.m
    wph
    @8
    cr
    wcel
    #
    cc0
    @8
    cle
    wbr
    wa
    @9
    cn0
    wcel
    @10
    cn
    wcel
    wph
    @8
    wph
    @7
    @2
    wph
    cX
    wph
    cX
    wph
    cX
    crp
    wcel
    #
    cY
    cX
    clt
    wbr
    #
    pntlem1.x
    simpld
    rpred
    #
    wph
    c1
    cY
    cX
    wph
    1red
    #
    wph
    cY
    wph
    cY
    crp
    wcel
    #
    c1
    cY
    cle
    wbr
    #
    pntlem1.y
    simpld
    rpred
    @14
    wph
    @16
    @17
    pntlem1.y
    simprd
    wph
    @12
    @13
    pntlem1.x
    simprd
    lelttrd
    rplogcld
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
    rpred
    wph
    @20
    @21
    @23
    wph
    @18
    @19
    @24
    @25
    simp3d
    simp2d
    rplogcld
    #
    rpdivcld
    #
    rprege0d
    @8
    flge0nn0
    @9
    nn0p1nn
    3syl
    syl5eqel
    #
    wph
    cM
    cz
    wcel
    cN
    cz
    wcel
    cM
    cN
    cle
    wbr
    #
    @0
    wph
    cM
    @28
    nnzd
    wph
    cN
    @3
    c2
    cdiv
    co
    #
    cfl
    cfv
    #
    cz
    pntlem1.n
    wph
    @30
    wph
    @3
    wph
    @1
    @2
    wph
    cZ
    wph
    cZ
    crp
    wcel
    #
    c1
    cZ
    clt
    wbr
    #
    ceu
    cZ
    csqrt
    cfv
    #
    cle
    wbr
    #
    @34
    cZ
    cY
    cdiv
    co
    cle
    wbr
    #
    w3a
    #
    c4
    cL
    cE
    cmul
    co
    cdiv
    co
    @34
    cle
    wbr
    #
    @8
    c2
    caddc
    co
    #
    @4
    cle
    wbr
    #
    cU
    c3
    cmul
    co
    cC
    caddc
    co
    @22
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
    @1
    cmul
    co
    cle
    wbr
    #
    w3a
    #
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
    #
    simp1d
    #
    relogcld
    @26
    rerpdivcld
    #
    rehalfcld
    #
    flcld
    syl5eqel
    #
    wph
    cc0
    @5
    cle
    wbr
    @29
    wph
    cc0
    @4
    @5
    wph
    0red
    wph
    @3
    cr
    wcel
    c4
    cn
    wcel
    @4
    cr
    wcel
    #
    @45
    4nn
    @3
    c4
    nndivre
    sylancl
    #
    wph
    cN
    cM
    wph
    cN
    @47
    zred
    #
    wph
    cM
    @28
    nnred
    #
    resubcld
    wph
    @4
    wph
    @3
    crp
    wcel
    c4
    crp
    wcel
    @4
    crp
    wcel
    wph
    @1
    @2
    wph
    cZ
    wph
    cZ
    @44
    rpred
    wph
    @33
    @35
    @36
    wph
    @32
    @37
    @42
    @43
    simp2d
    simp1d
    rplogcld
    @26
    rpdivcld
    c4
    4re
    4pos
    elrpii
    @3
    c4
    rpdivcl
    sylancl
    rpge0d
    wph
    @4
    cM
    caddc
    co
    #
    cN
    cle
    wbr
    #
    @6
    wph
    @53
    @52
    c1
    caddc
    co
    #
    cN
    c1
    caddc
    co
    #
    cle
    wbr
    wph
    @54
    @4
    cM
    c1
    caddc
    co
    #
    caddc
    co
    #
    @55
    cle
    wph
    @4
    cM
    c1
    wph
    @4
    @49
    recnd
    #
    wph
    cM
    @28
    nncnd
    wph
    1cnd
    #
    addassd
    wph
    @57
    @30
    @55
    wph
    @4
    @56
    @49
    wph
    cM
    c1
    @51
    @15
    readdcld
    #
    readdcld
    @46
    wph
    cN
    cr
    wcel
    #
    @55
    cr
    wcel
    @50
    cN
    peano2re
    syl
    wph
    @57
    @4
    @4
    caddc
    co
    #
    @30
    cle
    wph
    @56
    @4
    @4
    @60
    @49
    @49
    wph
    @56
    @39
    @4
    @60
    wph
    @8
    c2
    wph
    @8
    @27
    rpred
    #
    c2
    cr
    wcel
    wph
    2re
    a1i
    #
    readdcld
    @49
    wph
    @56
    @9
    c2
    caddc
    co
    #
    @39
    cle
    wph
    @10
    c1
    caddc
    co
    @9
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @56
    @65
    wph
    @9
    c1
    c1
    wph
    @9
    wph
    @11
    @9
    cr
    wcel
    @63
    @8
    reflcl
    syl
    #
    recnd
    @59
    @59
    addassd
    cM
    @10
    c1
    caddc
    pntlem1.m
    oveq1i
    c2
    @66
    @9
    caddc
    df-2
    oveq2i
    3eqtr4g
    wph
    @9
    @8
    c2
    @67
    @63
    @64
    wph
    @11
    @9
    @8
    cle
    wbr
    @63
    @8
    flle
    syl
    leadd1dd
    eqbrtrd
    wph
    @38
    @40
    @41
    wph
    @32
    @37
    @42
    @43
    simp3d
    simp2d
    letrd
    leadd2dd
    wph
    c2
    @30
    c2
    cdiv
    co
    #
    cmul
    co
    c2
    @4
    cmul
    co
    @30
    @62
    wph
    @68
    @4
    c2
    cmul
    wph
    @68
    @3
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    @4
    wph
    @3
    c2
    c2
    wph
    @3
    @45
    recnd
    wph
    2cnd
    #
    @70
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    #
    @71
    divdiv1d
    @69
    c4
    @3
    cdiv
    2t2e4
    oveq2i
    syl6eq
    oveq2d
    wph
    @30
    c2
    wph
    @30
    @46
    recnd
    @70
    @71
    divcan2d
    wph
    @4
    @58
    2timesd
    3eqtr3d
    breqtrrd
    wph
    @30
    @31
    c1
    caddc
    co
    #
    @55
    cle
    wph
    @30
    cr
    wcel
    @30
    @72
    cle
    wbr
    @46
    @30
    fllep1
    syl
    cN
    @31
    c1
    caddc
    pntlem1.n
    oveq1i
    syl6breqr
    letrd
    eqbrtrd
    wph
    @52
    cN
    c1
    wph
    @4
    cM
    @49
    @51
    readdcld
    @50
    @15
    leadd1d
    mpbird
    wph
    @48
    cM
    cr
    wcel
    @61
    @53
    @6
    wb
    @49
    @51
    @50
    @4
    cM
    cN
    leaddsub
    syl3anc
    mpbid
    #
    letrd
    wph
    cN
    cM
    @50
    @51
    subge0d
    mpbid
    cM
    cN
    eluz2
    syl3anbrc
    @73
    3jca
end
