include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "c8.mm"
include "cdiv.mm"
include "clog.mm"
include "cfv.mm"
include "chash.mm"
include "cv.mm"
include "cabs.mm"
include "csu.mm"
include "cc0.mm"
include "c1.mm"
include "cioo.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "crp.mm"
include "w3a.mm"
include "pntlemc.mm"
include "simp3d.mm"
include "pntlemd.mm"
include "simp1d.mm"
include "rpmulcld.mm"
include "cn.mm"
include "8nn.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "rpdivcl.mm"
include "sylancl.mm"
include "ceu.mm"
include "csqrt.mm"
include "cle.mm"
include "c4.mm"
include "c2.mm"
include "caddc.mm"
include "c3.mm"
include "cexp.mm"
include "cdc.mm"
include "pntlemb.mm"
include "rpred.mm"
include "simp2d.mm"
include "rplogcld.mm"
include "cfn.mm"
include "cn0.mm"
include "cfl.mm"
include "cfz.mm"
include "fzfid.mm"
include "syl5eqel.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0red.mm"
include "rpdivcld.mm"
include "relogcld.mm"
include "rerpdivcld.mm"
include "remulcld.mm"
include "wa.mm"
include "cr.mm"
include "adantr.mm"
include "cuz.mm"
include "cfzo.mm"
include "cz.mm"
include "elfzoelz.mm"
include "peano2zd.mm"
include "rpexpcld.mm"
include "rprege0d.mm"
include "flge0nn0.mm"
include "nn0p1nn.mm"
include "3syl.mm"
include "elfzuz.mm"
include "eleq2s.mm"
include "eluznn.mm"
include "syl2an.mm"
include "nndivred.mm"
include "nnrpd.mm"
include "pntrf.mm"
include "ffvelrni.mm"
include "recnd.mm"
include "abscld.mm"
include "resubcld.mm"
include "fsumrecl.mm"
include "pntlemr.mm"
include "cif.mm"
include "cc.mm"
include "wceq.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "wss.mm"
include "wral.mm"
include "wo.mm"
include "pntlemq.mm"
include "ralrimivw.mm"
include "olcd.mm"
include "sumss2.mm"
include "syl21anc.mm"
include "eqtr3d.mm"
include "adantlr.mm"
include "wn.mm"
include "0red.mm"
include "ifclda.mm"
include "breq1.mm"
include "rpregt0d.mm"
include "simpld.mm"
include "1rp.mm"
include "rpaddcl.mm"
include "sylancr.mm"
include "sselda.mm"
include "syldan.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "elfzle2.mm"
include "wb.mm"
include "elfzelz.mm"
include "flge.mm"
include "mpbird.mm"
include "nnred.mm"
include "ere.mm"
include "a1i.mm"
include "rpsqrtcld.mm"
include "cicc.mm"
include "simprd.mm"
include "rpcnd.mm"
include "mulcomd.mm"
include "pntlemg.mm"
include "elfzouz.mm"
include "nnnn0d.mm"
include "expp1d.mm"
include "eqtr4d.mm"
include "breqtrd.mm"
include "ltled.mm"
include "fzofzp1.mm"
include "pntlemh.mm"
include "mpdan.mm"
include "letrd.mm"
include "lemul2d.mm"
include "mpbid.mm"
include "remsqsqrt.mm"
include "lemuldivd.mm"
include "reflcl.mm"
include "peano2re.mm"
include "fllep1.mm"
include "elfzle1.mm"
include "logdivle.mm"
include "syl22anc.mm"
include "lemul2.mm"
include "syl3anc.mm"
include "wne.mm"
include "rpcnne0d.mm"
include "div23.mm"
include "divass.mm"
include "log1.mm"
include "nnge1d.mm"
include "logleb.mm"
include "syl5eqbrr.mm"
include "divsubdir.mm"
include "divdiv2.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "absmuld.mm"
include "absid.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "lemuldiv2.mm"
include "lediv23.mm"
include "elicc2.mm"
include "mpbir3and.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqbrtrrd.mm"
include "lesub2dd.mm"
include "eqbrtrd.mm"
include "lemul1ad.mm"
include "nnzd.mm"
include "elfzofz.mm"
include "lediv2d.mm"
include "jca.mm"
include "pntlemn.mm"
include "ifbothda.mm"
include "fsumle.mm"

theorem pntlemj
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cU: class U
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vx: setvar x
  let vw: setvar w
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vv: setvar v
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vl: setvar l
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
  assume pntlem1.K: |- ( ph -> A. y e. ( X (,) +oo ) E. z e. RR+ ( ( y < z /\ ( ( 1 + ( L x. E ) ) x. z ) < ( K x. y ) ) /\ A. u e. ( z [,] ( ( 1 + ( L x. E ) ) x. z ) ) ( abs ` ( ( R ` u ) / u ) ) <_ E ) )
  assume pntlem1.o: |- O = ( ( ( |_ ` ( Z / ( K ^ ( J + 1 ) ) ) ) + 1 ) ... ( |_ ` ( Z / ( K ^ J ) ) ) )
  assume pntlem1.v: |- ( ph -> V e. RR+ )
  assume pntlem1.V: |- ( ph -> ( ( ( K ^ J ) < V /\ ( ( 1 + ( L x. E ) ) x. V ) < ( K x. ( K ^ J ) ) ) /\ A. u e. ( V [,] ( ( 1 + ( L x. E ) ) x. V ) ) ( abs ` ( ( R ` u ) / u ) ) <_ E ) )
  assume pntlem1.j: |- ( ph -> J e. ( M ..^ N ) )
  assume pntlem1.i: |- I = ( ( ( |_ ` ( Z / ( ( 1 + ( L x. E ) ) x. V ) ) ) + 1 ) ... ( |_ ` ( Z / V ) ) )

  disjoint C z
  disjoint I n
  disjoint n y
  disjoint n z
  disjoint J n
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint n u
  disjoint L n
  disjoint u y
  disjoint u z
  disjoint L u
  disjoint L y
  disjoint L z
  disjoint K n
  disjoint K y
  disjoint K z
  disjoint M n
  disjoint M z
  disjoint O n
  disjoint O z
  disjoint n ph
  disjoint N n
  disjoint N z
  disjoint R n
  disjoint R u
  disjoint R y
  disjoint R z
  disjoint V n
  disjoint V u
  disjoint U n
  disjoint U z
  disjoint W n
  disjoint W z
  disjoint X n
  disjoint X y
  disjoint X z
  disjoint Y n
  disjoint Y z
  disjoint a n
  disjoint a u
  disjoint a y
  disjoint a z
  disjoint E a
  disjoint E n
  disjoint E u
  disjoint E y
  disjoint E z
  disjoint Z n
  disjoint Z u
  disjoint Z z
  disjoint x z
  disjoint C x
  disjoint F w
  disjoint n x
  disjoint x y
  disjoint J x
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
  disjoint u x
  disjoint L x
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K x
  disjoint M j
  disjoint M m
  disjoint M x
  disjoint O x
  disjoint j v
  disjoint j ph
  disjoint m v
  disjoint m ph
  disjoint n v
  disjoint v x
  disjoint ph v
  disjoint ph x
  disjoint N j
  disjoint N m
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
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint R v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint R w
  disjoint R x
  disjoint U j
  disjoint U m
  disjoint U w
  disjoint U x
  disjoint W v
  disjoint W w
  disjoint X k
  disjoint Y i
  disjoint Y j
  disjoint Y m
  disjoint Y x
  disjoint a e
  disjoint a g
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a v
  disjoint a x
  disjoint E e
  disjoint E g
  disjoint E j
  disjoint E k
  disjoint E m
  disjoint E v
  disjoint E x
  disjoint Z j
  disjoint Z m
  disjoint Z x
  assert |- ( ph -> ( ( U - E ) x. ( ( ( L x. E ) / 8 ) x. ( log ` Z ) ) ) <_ sum_ n e. O ( ( ( U / n ) - ( abs ` ( ( R ` ( Z / n ) ) / Z ) ) ) x. ( log ` n ) ) )

  proof
    wph
    cU
    cE
    cmin
    co
    #
    cL
    cE
    cmul
    co
    #
    c8
    cdiv
    co
    #
    cZ
    clog
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cI
    chash
    cfv
    #
    @0
    cZ
    cV
    cdiv
    co
    #
    clog
    cfv
    #
    @7
    cdiv
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    cO
    cU
    vn
    cv
    #
    cdiv
    co
    #
    cZ
    @12
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
    @12
    clog
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    wph
    @5
    wph
    @0
    @4
    wph
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
    @0
    crp
    wcel
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
    @22
    @23
    @24
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
    simp3d
    simp3d
    #
    wph
    @2
    @3
    wph
    @1
    crp
    wcel
    #
    c8
    crp
    wcel
    #
    @2
    crp
    wcel
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
    wph
    @25
    @26
    @27
    @28
    simp1d
    #
    rpmulcld
    #
    c8
    cn
    wcel
    @31
    8nn
    c8
    nnrp
    ax-mp
    @1
    c8
    rpdivcl
    sylancl
    wph
    cZ
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
    @36
    cZ
    cY
    cdiv
    co
    #
    cle
    wbr
    #
    w3a
    #
    c4
    @1
    cdiv
    co
    @36
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
    @3
    @41
    cdiv
    co
    c4
    cdiv
    co
    #
    cle
    wbr
    cU
    c3
    cmul
    co
    cC
    caddc
    co
    @0
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
    @3
    cmul
    co
    cle
    wbr
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
    rpred
    #
    wph
    @35
    @37
    @39
    wph
    @34
    @40
    @43
    @44
    simp2d
    #
    simp1d
    rplogcld
    rpmulcld
    rpmulcld
    rpred
    wph
    @6
    @10
    wph
    @6
    wph
    cI
    cfn
    wcel
    #
    @6
    cn0
    wcel
    wph
    cI
    cZ
    c1
    @1
    caddc
    co
    #
    cV
    cmul
    co
    #
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
    @7
    cfl
    cfv
    #
    cfz
    co
    #
    cfn
    pntlem1.i
    wph
    @53
    @54
    fzfid
    syl5eqel
    #
    cI
    hashcl
    syl
    nn0red
    wph
    @0
    @9
    wph
    @0
    @29
    rpred
    #
    wph
    @8
    @7
    wph
    @7
    wph
    cZ
    cV
    @45
    pntlem1.v
    rpdivcld
    #
    relogcld
    @58
    rerpdivcld
    #
    remulcld
    #
    remulcld
    wph
    cO
    @20
    vn
    wph
    cO
    cZ
    cK
    cJ
    c1
    caddc
    co
    #
    cexp
    co
    #
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
    cZ
    cK
    cJ
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cfz
    co
    #
    cfn
    pntlem1.o
    wph
    @65
    @68
    fzfid
    syl5eqel
    #
    wph
    @12
    cO
    wcel
    #
    wa
    #
    @18
    @19
    @72
    @13
    @17
    @72
    cU
    @12
    wph
    cU
    cr
    wcel
    @71
    wph
    cU
    pntlem1.u
    rpred
    adantr
    wph
    @65
    cn
    wcel
    #
    @12
    @65
    cuz
    cfv
    wcel
    #
    @12
    cn
    wcel
    #
    @71
    wph
    @63
    cr
    wcel
    cc0
    @63
    cle
    wbr
    wa
    @64
    cn0
    wcel
    @73
    wph
    @63
    wph
    cZ
    @62
    @45
    wph
    cK
    @61
    wph
    @25
    @26
    @27
    @28
    simp2d
    #
    wph
    cJ
    wph
    cJ
    cM
    cN
    cfzo
    co
    wcel
    #
    cJ
    cz
    wcel
    pntlem1.j
    cJ
    cM
    cN
    elfzoelz
    syl
    #
    peano2zd
    rpexpcld
    #
    rpdivcld
    rprege0d
    @63
    flge0nn0
    @64
    nn0p1nn
    3syl
    @74
    @12
    @69
    cO
    @12
    @65
    @68
    elfzuz
    pntlem1.o
    eleq2s
    @12
    @65
    eluznn
    syl2an
    #
    nndivred
    #
    @72
    @16
    @72
    @16
    @72
    @15
    cZ
    @72
    @14
    crp
    wcel
    @15
    cr
    wcel
    #
    @72
    cZ
    @12
    wph
    @34
    @71
    @45
    adantr
    #
    @72
    @12
    @80
    nnrpd
    #
    rpdivcld
    crp
    cr
    @14
    cR
    cR
    va
    pntlem1.r
    pntrf
    ffvelrni
    syl
    #
    @83
    rerpdivcld
    recnd
    #
    abscld
    #
    resubcld
    #
    @72
    @12
    @84
    relogcld
    remulcld
    #
    fsumrecl
    wph
    vy
    vz
    vu
    cA
    cB
    cC
    cD
    cR
    cU
    cE
    cF
    cI
    cJ
    cK
    cL
    cM
    cN
    cO
    cV
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
    pntlem1.U
    pntlem1.K
    pntlem1.o
    pntlem1.v
    pntlem1.V
    pntlem1.j
    pntlem1.i
    pntlemr
    wph
    @11
    cO
    @12
    cI
    wcel
    #
    @10
    cc0
    cif
    #
    vn
    csu
    #
    @21
    cle
    wph
    cI
    @10
    vn
    csu
    #
    @11
    @92
    wph
    @48
    @10
    cc
    wcel
    #
    @93
    @11
    wceq
    @56
    wph
    @10
    @60
    recnd
    #
    cI
    @10
    vn
    fsumconst
    syl2anc
    wph
    cI
    cO
    wss
    @94
    vn
    cI
    wral
    cO
    c1
    cuz
    cfv
    wss
    #
    cO
    cfn
    wcel
    #
    wo
    @93
    @92
    wceq
    wph
    vy
    vz
    vu
    cA
    cB
    cC
    cD
    cR
    cU
    cE
    cF
    cI
    cJ
    cK
    cL
    cM
    cN
    cO
    cV
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
    pntlem1.U
    pntlem1.K
    pntlem1.o
    pntlem1.v
    pntlem1.V
    pntlem1.j
    pntlem1.i
    pntlemq
    #
    wph
    @94
    vn
    cI
    @95
    ralrimivw
    wph
    @97
    @96
    @70
    olcd
    cI
    cO
    @10
    vn
    c1
    sumss2
    syl21anc
    eqtr3d
    wph
    cO
    @91
    @20
    vn
    @70
    @72
    @90
    @10
    cc0
    cr
    wph
    @90
    @10
    cr
    wcel
    #
    @71
    wph
    @99
    @90
    @60
    adantr
    #
    adantlr
    @72
    @90
    wn
    #
    wa
    0red
    ifclda
    @89
    @90
    @10
    @20
    cle
    wbr
    #
    cc0
    @20
    cle
    wbr
    #
    @91
    @20
    cle
    wbr
    @72
    @10
    cc0
    @10
    @91
    @20
    cle
    breq1
    cc0
    @91
    @20
    cle
    breq1
    wph
    @90
    @102
    @71
    wph
    @90
    wa
    #
    @10
    @0
    @19
    @12
    cdiv
    co
    #
    cmul
    co
    #
    @20
    @100
    @104
    @0
    @105
    @104
    @0
    cr
    wcel
    #
    cc0
    @0
    clt
    wbr
    #
    wph
    @107
    @108
    wa
    #
    @90
    wph
    @0
    @29
    rpregt0d
    adantr
    #
    simpld
    @104
    @19
    @12
    @104
    @12
    @104
    @12
    wph
    @53
    cn
    wcel
    #
    @12
    @53
    cuz
    cfv
    wcel
    #
    @75
    @90
    wph
    @51
    cr
    wcel
    #
    cc0
    @51
    cle
    wbr
    wa
    @52
    cn0
    wcel
    @111
    wph
    @51
    wph
    cZ
    @50
    @45
    wph
    @49
    cV
    wph
    c1
    crp
    wcel
    #
    @30
    @49
    crp
    wcel
    1rp
    @33
    c1
    @1
    rpaddcl
    sylancr
    pntlem1.v
    rpmulcld
    #
    rpdivcld
    #
    rprege0d
    @51
    flge0nn0
    @52
    nn0p1nn
    3syl
    @112
    @12
    @55
    cI
    @12
    @53
    @54
    elfzuz
    pntlem1.i
    eleq2s
    @12
    @53
    eluznn
    syl2an
    #
    nnrpd
    #
    relogcld
    #
    @117
    nndivred
    #
    remulcld
    wph
    @90
    @71
    @20
    cr
    wcel
    wph
    cI
    cO
    @12
    @98
    sselda
    #
    @89
    syldan
    @104
    @9
    @105
    cle
    wbr
    #
    @10
    @106
    cle
    wbr
    #
    @104
    @12
    @7
    cle
    wbr
    #
    @122
    @104
    @124
    @12
    @54
    cle
    wbr
    #
    @104
    @12
    @55
    wcel
    #
    @125
    @104
    @12
    cI
    @55
    wph
    @90
    simpr
    pntlem1.i
    syl6eleq
    #
    @12
    @53
    @54
    elfzle2
    syl
    @104
    @7
    cr
    wcel
    #
    @12
    cz
    wcel
    #
    @124
    @125
    wb
    wph
    @128
    @90
    wph
    @7
    @58
    rpred
    adantr
    #
    @104
    @126
    @129
    @127
    @12
    @53
    @54
    elfzelz
    syl
    @7
    @12
    flge
    syl2anc
    mpbird
    #
    @104
    @12
    cr
    wcel
    #
    ceu
    @12
    cle
    wbr
    @128
    ceu
    @7
    cle
    wbr
    @124
    @122
    wb
    @104
    @12
    @117
    nnred
    #
    @104
    ceu
    @51
    @12
    ceu
    cr
    wcel
    #
    @104
    ere
    a1i
    #
    wph
    @113
    @90
    wph
    @51
    @116
    rpred
    #
    adantr
    #
    @133
    wph
    ceu
    @51
    cle
    wbr
    @90
    wph
    ceu
    @36
    @51
    @134
    wph
    ere
    a1i
    wph
    @36
    wph
    cZ
    @45
    rpsqrtcld
    #
    rpred
    #
    @136
    wph
    @35
    @37
    @39
    @47
    simp2d
    wph
    @36
    @50
    cmul
    co
    #
    cZ
    cle
    wbr
    @36
    @51
    cle
    wbr
    wph
    @140
    @36
    @36
    cmul
    co
    #
    cZ
    cle
    wph
    @50
    @36
    cle
    wbr
    @140
    @141
    cle
    wbr
    wph
    @50
    @62
    @36
    wph
    @50
    @115
    rpred
    #
    wph
    @62
    @79
    rpred
    #
    @139
    wph
    @50
    @62
    @142
    @143
    wph
    @50
    cK
    @66
    cmul
    co
    #
    @62
    clt
    wph
    @66
    cV
    clt
    wbr
    #
    @50
    @144
    clt
    wbr
    #
    wph
    @145
    @146
    wa
    #
    vu
    cv
    #
    cR
    cfv
    #
    @148
    cdiv
    co
    #
    cabs
    cfv
    #
    cE
    cle
    wbr
    #
    vu
    cV
    @50
    cicc
    co
    #
    wral
    #
    pntlem1.V
    simpld
    simprd
    wph
    @144
    @66
    cK
    cmul
    co
    @62
    wph
    cK
    @66
    wph
    cK
    @76
    rpcnd
    #
    wph
    @66
    wph
    cK
    cJ
    @76
    @78
    rpexpcld
    #
    rpcnd
    mulcomd
    wph
    cK
    cJ
    @155
    wph
    cJ
    wph
    cM
    cn
    wcel
    #
    cJ
    cM
    cuz
    cfv
    #
    wcel
    #
    cJ
    cn
    wcel
    wph
    @157
    cN
    @158
    wcel
    @42
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
    wph
    @77
    @159
    pntlem1.j
    cJ
    cM
    cN
    elfzouz
    syl
    cJ
    cM
    eluznn
    syl2anc
    nnnn0d
    expp1d
    eqtr4d
    breqtrd
    ltled
    wph
    cX
    @62
    clt
    wbr
    #
    @62
    @36
    cle
    wbr
    #
    wph
    @61
    cM
    cN
    cfz
    co
    #
    wcel
    #
    @160
    @161
    wa
    wph
    @77
    @163
    pntlem1.j
    cM
    cN
    cJ
    fzofzp1
    syl
    wph
    cA
    cB
    cC
    cD
    cR
    cU
    cE
    cF
    @61
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
    pntlemh
    mpdan
    simprd
    letrd
    wph
    @50
    @36
    @36
    @142
    @139
    @138
    lemul2d
    mpbid
    wph
    cZ
    cr
    wcel
    #
    cc0
    cZ
    cle
    wbr
    wa
    @141
    cZ
    wceq
    wph
    cZ
    @45
    rprege0d
    cZ
    remsqsqrt
    syl
    breqtrd
    wph
    @36
    cZ
    @50
    @139
    @46
    @115
    lemuldivd
    mpbid
    letrd
    adantr
    @104
    @51
    @53
    @12
    @137
    wph
    @53
    cr
    wcel
    #
    @90
    wph
    @113
    @52
    cr
    wcel
    @165
    @136
    @51
    reflcl
    @52
    peano2re
    3syl
    adantr
    @133
    @104
    @113
    @51
    @53
    cle
    wbr
    @137
    @51
    fllep1
    syl
    @104
    @126
    @53
    @12
    cle
    wbr
    @127
    @12
    @53
    @54
    elfzle1
    syl
    letrd
    #
    letrd
    #
    @130
    @104
    ceu
    @12
    @7
    @135
    @133
    @130
    @167
    @131
    letrd
    @12
    @7
    logdivle
    syl22anc
    mpbid
    @104
    @9
    cr
    wcel
    #
    @105
    cr
    wcel
    @109
    @122
    @123
    wb
    wph
    @168
    @90
    @59
    adantr
    @120
    @110
    @9
    @105
    @0
    lemul2
    syl3anc
    mpbid
    @104
    @0
    @12
    cdiv
    co
    #
    @19
    cmul
    co
    #
    @106
    @20
    cle
    @104
    @0
    @19
    cmul
    co
    @12
    cdiv
    co
    #
    @170
    @106
    @104
    @0
    cc
    wcel
    #
    @19
    cc
    wcel
    #
    @12
    cc
    wcel
    #
    @12
    cc0
    wne
    wa
    #
    @171
    @170
    wceq
    wph
    @172
    @90
    wph
    @0
    @29
    rpcnd
    adantr
    #
    @104
    @19
    @119
    recnd
    #
    @104
    @12
    @118
    rpcnne0d
    #
    @0
    @19
    @12
    div23
    syl3anc
    @104
    @172
    @173
    @175
    @171
    @106
    wceq
    @176
    @177
    @178
    @0
    @19
    @12
    divass
    syl3anc
    eqtr3d
    @104
    @169
    @18
    @19
    @104
    @0
    @12
    wph
    @107
    @90
    @57
    adantr
    @117
    nndivred
    wph
    @90
    @71
    @18
    cr
    wcel
    @121
    @88
    syldan
    @119
    @104
    cc0
    c1
    clog
    cfv
    #
    @19
    cle
    log1
    @104
    c1
    @12
    cle
    wbr
    #
    @179
    @19
    cle
    wbr
    #
    @104
    @12
    @117
    nnge1d
    @104
    @114
    @12
    crp
    wcel
    @180
    @181
    wb
    1rp
    @118
    c1
    @12
    logleb
    sylancr
    mpbid
    syl5eqbrr
    @104
    @169
    @13
    cE
    @12
    cdiv
    co
    #
    cmin
    co
    #
    @18
    cle
    @104
    cU
    cc
    wcel
    #
    cE
    cc
    wcel
    @175
    @169
    @183
    wceq
    wph
    @184
    @90
    wph
    cU
    pntlem1.u
    rpcnd
    adantr
    @104
    cE
    wph
    cE
    cr
    wcel
    @90
    wph
    cE
    @32
    rpred
    adantr
    #
    recnd
    @178
    cU
    cE
    @12
    divsubdir
    syl3anc
    @104
    @17
    @182
    @13
    wph
    @90
    @71
    @17
    cr
    wcel
    @121
    @87
    syldan
    #
    @104
    cE
    @12
    @185
    @117
    nndivred
    wph
    @90
    @71
    @13
    cr
    wcel
    @121
    @81
    syldan
    @104
    @17
    @12
    cmul
    co
    #
    cE
    cle
    wbr
    @17
    @182
    cle
    wbr
    @104
    @15
    @14
    cdiv
    co
    #
    cabs
    cfv
    #
    @187
    cE
    cle
    @104
    @189
    @16
    @12
    cmul
    co
    #
    cabs
    cfv
    @17
    @12
    cabs
    cfv
    #
    cmul
    co
    @187
    @104
    @188
    @190
    cabs
    @104
    @188
    @15
    @12
    cmul
    co
    cZ
    cdiv
    co
    #
    @190
    @104
    @15
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
    @175
    @188
    @192
    wceq
    @104
    @15
    wph
    @90
    @71
    @82
    @121
    @85
    syldan
    recnd
    #
    @104
    cZ
    wph
    @34
    @90
    @45
    adantr
    rpcnne0d
    #
    @178
    @15
    cZ
    @12
    divdiv2
    syl3anc
    @104
    @193
    @174
    @194
    @192
    @190
    wceq
    @195
    @104
    @12
    @118
    rpcnd
    #
    @196
    @15
    @12
    cZ
    div23
    syl3anc
    eqtrd
    fveq2d
    @104
    @16
    @12
    wph
    @90
    @71
    @16
    cc
    wcel
    @121
    @86
    syldan
    @197
    absmuld
    @104
    @191
    @12
    @17
    cmul
    @104
    @132
    cc0
    @12
    cle
    wbr
    wa
    @191
    @12
    wceq
    @104
    @12
    @118
    rprege0d
    @12
    absid
    syl
    oveq2d
    3eqtrd
    @104
    @14
    @153
    wcel
    #
    @154
    @189
    cE
    cle
    wbr
    #
    @104
    @198
    @14
    cr
    wcel
    #
    cV
    @14
    cle
    wbr
    #
    @14
    @50
    cle
    wbr
    #
    @104
    cZ
    @12
    wph
    @164
    @90
    @46
    adantr
    #
    @117
    nndivred
    @104
    cV
    @12
    cmul
    co
    cZ
    cle
    wbr
    #
    @201
    @104
    @204
    @124
    @131
    @104
    @132
    @164
    cV
    cr
    wcel
    #
    cc0
    cV
    clt
    wbr
    #
    wa
    #
    @204
    @124
    wb
    @133
    @203
    wph
    @207
    @90
    wph
    cV
    pntlem1.v
    rpregt0d
    adantr
    #
    @12
    cZ
    cV
    lemuldiv2
    syl3anc
    mpbird
    @104
    cV
    cZ
    @12
    @104
    @205
    @206
    @208
    simpld
    @203
    @118
    lemuldivd
    mpbid
    @104
    @51
    @12
    cle
    wbr
    #
    @202
    @166
    @104
    @164
    @50
    cr
    wcel
    #
    cc0
    @50
    clt
    wbr
    wa
    #
    @132
    cc0
    @12
    clt
    wbr
    wa
    @209
    @202
    wb
    @203
    wph
    @211
    @90
    wph
    @50
    @115
    rpregt0d
    adantr
    @104
    @12
    @118
    rpregt0d
    cZ
    @50
    @12
    lediv23
    syl3anc
    mpbid
    @104
    @205
    @210
    @198
    @200
    @201
    @202
    w3a
    wb
    wph
    @205
    @90
    wph
    cV
    pntlem1.v
    rpred
    adantr
    wph
    @210
    @90
    @142
    adantr
    cV
    @50
    @14
    elicc2
    syl2anc
    mpbir3and
    wph
    @154
    @90
    wph
    @147
    @154
    pntlem1.V
    simprd
    adantr
    @152
    @199
    vu
    @14
    @153
    @148
    @14
    wceq
    #
    @151
    @189
    cE
    cle
    @212
    @150
    @188
    cabs
    @212
    @149
    @15
    @148
    @14
    cdiv
    @148
    @14
    cR
    fveq2
    @212
    id
    oveq12d
    fveq2d
    breq1d
    rspcv
    sylc
    eqbrtrrd
    @104
    @17
    cE
    @12
    @186
    @185
    @118
    lemuldivd
    mpbid
    lesub2dd
    eqbrtrd
    lemul1ad
    eqbrtrrd
    letrd
    adantlr
    @72
    @103
    @101
    wph
    @71
    @75
    @12
    @38
    cle
    wbr
    #
    wa
    @103
    @72
    @75
    @213
    @80
    @72
    @12
    @67
    @38
    @72
    @12
    @80
    nnred
    wph
    @67
    cr
    wcel
    #
    @71
    wph
    @67
    wph
    cZ
    @66
    @45
    @156
    rpdivcld
    rpred
    adantr
    #
    wph
    @38
    cr
    wcel
    @71
    wph
    @38
    wph
    cZ
    cY
    @45
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
    #
    rpdivcld
    rpred
    adantr
    @72
    @12
    @67
    cle
    wbr
    #
    @12
    @68
    cle
    wbr
    #
    @72
    @12
    @69
    wcel
    @218
    @72
    @12
    cO
    @69
    wph
    @71
    simpr
    pntlem1.o
    syl6eleq
    @12
    @65
    @68
    elfzle2
    syl
    @72
    @214
    @129
    @217
    @218
    wb
    @215
    @72
    @12
    @80
    nnzd
    @67
    @12
    flge
    syl2anc
    mpbird
    wph
    @67
    @38
    cle
    wbr
    #
    @71
    wph
    cY
    @66
    cle
    wbr
    @219
    wph
    cY
    cX
    @66
    wph
    cY
    @216
    rpred
    #
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
    @66
    @156
    rpred
    #
    wph
    cY
    cX
    @220
    @223
    wph
    @221
    @222
    pntlem1.x
    simprd
    ltled
    wph
    cX
    @66
    @223
    @224
    wph
    cX
    @66
    clt
    wbr
    #
    @66
    @36
    cle
    wbr
    #
    wph
    cJ
    @162
    wcel
    #
    @225
    @226
    wa
    wph
    @77
    @227
    pntlem1.j
    cJ
    cM
    cN
    elfzofz
    syl
    wph
    cA
    cB
    cC
    cD
    cR
    cU
    cE
    cF
    cJ
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
    pntlemh
    mpdan
    simpld
    ltled
    letrd
    wph
    cY
    @66
    cZ
    @216
    @156
    @45
    lediv2d
    mpbid
    adantr
    letrd
    jca
    wph
    vz
    cA
    cB
    cC
    cD
    cR
    cU
    cE
    cF
    @12
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
    pntlem1.U
    pntlemn
    syldan
    adantr
    ifbothda
    fsumle
    eqbrtrd
    letrd
end
