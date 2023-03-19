include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "ceu.mm"
include "csqrt.mm"
include "cfv.mm"
include "cle.mm"
include "cdiv.mm"
include "co.mm"
include "w3a.mm"
include "c4.mm"
include "cmul.mm"
include "clog.mm"
include "c2.mm"
include "caddc.mm"
include "c3.mm"
include "cmin.mm"
include "cexp.mm"
include "cdc.mm"
include "cr.mm"
include "cpnf.mm"
include "cico.mm"
include "cxr.mm"
include "wb.mm"
include "pntlema.mm"
include "rpred.mm"
include "pnfxr.mm"
include "elico2.mm"
include "sylancl.mm"
include "mpbid.mm"
include "simp1d.mm"
include "simp2d.mm"
include "rpgecld.mm"
include "1re.mm"
include "a1i.mm"
include "ere.mm"
include "rpsqrtcld.mm"
include "1lt2.mm"
include "egt2lt3.mm"
include "simpli.mm"
include "2re.mm"
include "lttri.mm"
include "mp2an.mm"
include "4re.mm"
include "simpri.mm"
include "3lt4.mm"
include "3re.mm"
include "cn.mm"
include "4nn.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "pntlemd.mm"
include "cc0.mm"
include "cioo.mm"
include "pntlemc.mm"
include "rpmulcld.mm"
include "rpdivcl.mm"
include "sylancr.mm"
include "wa.mm"
include "eliooord.mm"
include "syl.mm"
include "simprd.mm"
include "ltmul1dd.mm"
include "rpcnd.mm"
include "mulid2d.mm"
include "breqtrd.mm"
include "simp3d.mm"
include "lttrd.mm"
include "4pos.mm"
include "jctir.mm"
include "ltmul2.mm"
include "syl3anc.mm"
include "4cn.mm"
include "mulid1i.mm"
include "syl6breq.mm"
include "ltmuldivd.mm"
include "simpld.mm"
include "rpaddcld.mm"
include "ltaddrp2d.mm"
include "resqcld.mm"
include "ce.mm"
include "cz.mm"
include "2z.mm"
include "rpexpcl.mm"
include "4z.mm"
include "3nn0.mm"
include "2nn.mm"
include "decnncl.mm"
include "rpmulcl.mm"
include "rpdivcld.mm"
include "3nn.mm"
include "rpefcld.mm"
include "ltaddrpd.mm"
include "syl6breqr.mm"
include "ltletrd.mm"
include "wceq.mm"
include "rprege0d.mm"
include "resqrtth.mm"
include "breqtrrd.mm"
include "lt2sq.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "0le1.mm"
include "syl21anc.mm"
include "sq1.mm"
include "3brtr3d.mm"
include "ltled.mm"
include "rerpdivcld.mm"
include "ltmul2dd.mm"
include "remsqsqrt.mm"
include "3jca.mm"
include "relogcld.mm"
include "rplogcld.mm"
include "readdcl.mm"
include "nndivre.mm"
include "relogexp.mm"
include "recnd.mm"
include "addcomd.mm"
include "syl5eq.mm"
include "logltb.mm"
include "eqbrtrrd.mm"
include "ltmuldiv2.mm"
include "ltdiv1dd.mm"
include "relogmuld.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "cc.mm"
include "wne.mm"
include "2cnd.mm"
include "mulcld.mm"
include "rpcnne0d.mm"
include "divdir.mm"
include "divcan4d.mm"
include "3eqtrd.mm"
include "rpcnne0.mm"
include "mp1i.mm"
include "divdiv32.mm"
include "remulcld.mm"
include "divdiv2.mm"
include "mulcomd.mm"
include "div23.mm"
include "reefcld.mm"
include "reeflogd.mm"
include "eflt.mm"
include "eqbrtrd.mm"
include "ltdivmuld.mm"
include "divass.mm"

theorem pntlemb
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
  assert |- ( ph -> ( Z e. RR+ /\ ( 1 < Z /\ _e <_ ( sqrt ` Z ) /\ ( sqrt ` Z ) <_ ( Z / Y ) ) /\ ( ( 4 / ( L x. E ) ) <_ ( sqrt ` Z ) /\ ( ( ( log ` X ) / ( log ` K ) ) + 2 ) <_ ( ( ( log ` Z ) / ( log ` K ) ) / 4 ) /\ ( ( U x. 3 ) + C ) <_ ( ( ( U - E ) x. ( ( L x. ( E ^ 2 ) ) / ( ; 3 2 x. B ) ) ) x. ( log ` Z ) ) ) ) )

  proof
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
    @2
    cZ
    cY
    cdiv
    co
    #
    cle
    wbr
    #
    w3a
    c4
    cL
    cE
    cmul
    co
    #
    cdiv
    co
    #
    @2
    cle
    wbr
    #
    cX
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
    c2
    caddc
    co
    #
    cZ
    clog
    cfv
    #
    @10
    cdiv
    co
    #
    c4
    cdiv
    co
    #
    cle
    wbr
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
    c3
    c2
    cdc
    #
    cB
    cmul
    co
    #
    cdiv
    co
    cmul
    co
    #
    @13
    cmul
    co
    #
    cle
    wbr
    #
    w3a
    wph
    cZ
    cW
    wph
    cZ
    cr
    wcel
    #
    cW
    cZ
    cle
    wbr
    #
    cZ
    cpnf
    clt
    wbr
    #
    wph
    cZ
    cW
    cpnf
    cico
    co
    wcel
    #
    @27
    @28
    @29
    w3a
    #
    pntlem1.z
    wph
    cW
    cr
    wcel
    cpnf
    cxr
    wcel
    @30
    @31
    wb
    wph
    cW
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
    pntlema
    #
    rpred
    #
    pnfxr
    cW
    cpnf
    cZ
    elico2
    sylancl
    mpbid
    #
    simp1d
    #
    @32
    wph
    @27
    @28
    @29
    @34
    simp2d
    #
    rpgecld
    #
    wph
    @1
    @3
    @5
    wph
    c1
    c2
    cexp
    co
    #
    @2
    c2
    cexp
    co
    #
    c1
    cZ
    clt
    wph
    c1
    @2
    clt
    wbr
    #
    @38
    @39
    clt
    wbr
    #
    wph
    c1
    ceu
    @2
    c1
    cr
    wcel
    #
    wph
    1re
    a1i
    #
    ceu
    cr
    wcel
    wph
    ere
    a1i
    #
    wph
    @2
    wph
    cZ
    @37
    rpsqrtcld
    #
    rpred
    #
    c1
    ceu
    clt
    wbr
    #
    wph
    c1
    c2
    clt
    wbr
    c2
    ceu
    clt
    wbr
    #
    @47
    1lt2
    @48
    ceu
    c3
    clt
    wbr
    #
    egt2lt3
    simpli
    c1
    c2
    ceu
    1re
    2re
    ere
    lttri
    mp2an
    a1i
    wph
    ceu
    c4
    @2
    @44
    c4
    cr
    wcel
    #
    wph
    4re
    a1i
    #
    @46
    ceu
    c4
    clt
    wbr
    #
    wph
    @49
    c3
    c4
    clt
    wbr
    @52
    @48
    @49
    egt2lt3
    simpri
    3lt4
    ceu
    c3
    c4
    ere
    3re
    4re
    lttri
    mp2an
    a1i
    wph
    c4
    @7
    @2
    @51
    wph
    @7
    wph
    c4
    crp
    wcel
    #
    @6
    crp
    wcel
    @7
    crp
    wcel
    c4
    cn
    wcel
    #
    @53
    4nn
    c4
    nnrp
    ax-mp
    #
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
    #
    wcel
    #
    c1
    cK
    clt
    wbr
    #
    @19
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
    #
    c4
    @6
    rpdivcl
    sylancr
    #
    rpred
    #
    @46
    wph
    c4
    @6
    cmul
    co
    #
    c4
    clt
    wbr
    c4
    @7
    clt
    wbr
    wph
    @69
    c4
    c1
    cmul
    co
    #
    c4
    clt
    wph
    @6
    c1
    clt
    wbr
    #
    @69
    @70
    clt
    wbr
    #
    wph
    @6
    cE
    c1
    wph
    @6
    @66
    rpred
    #
    wph
    cE
    @65
    rpred
    @43
    wph
    @6
    c1
    cE
    cmul
    co
    cE
    clt
    wph
    cL
    c1
    cE
    wph
    cL
    @56
    rpred
    @43
    @65
    wph
    cc0
    cL
    clt
    wbr
    #
    cL
    c1
    clt
    wbr
    #
    wph
    cL
    @59
    wcel
    @74
    @75
    wa
    pntlem1.l
    cL
    cc0
    c1
    eliooord
    syl
    simprd
    ltmul1dd
    wph
    cE
    wph
    cE
    @65
    rpcnd
    mulid2d
    breqtrd
    wph
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
    wph
    @60
    @76
    @77
    wa
    wph
    @60
    @61
    @62
    wph
    @57
    @58
    @63
    @64
    simp3d
    #
    simp1d
    cE
    cc0
    c1
    eliooord
    syl
    simprd
    lttrd
    wph
    @6
    cr
    wcel
    @42
    @50
    cc0
    c4
    clt
    wbr
    #
    wa
    #
    @71
    @72
    wb
    @73
    @43
    wph
    @50
    @79
    @51
    4pos
    jctir
    #
    @6
    c1
    c4
    ltmul2
    syl3anc
    mpbid
    c4
    4cn
    mulid1i
    syl6breq
    wph
    c4
    c4
    @6
    @51
    @51
    @66
    ltmuldivd
    mpbid
    wph
    @7
    cY
    @7
    caddc
    co
    #
    @2
    @68
    wph
    @82
    wph
    cY
    @7
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
    @67
    rpaddcld
    #
    rpred
    #
    @46
    wph
    @7
    cY
    @68
    @83
    ltaddrp2d
    wph
    @82
    @2
    clt
    wbr
    #
    @82
    c2
    cexp
    co
    #
    @39
    clt
    wbr
    #
    wph
    @87
    cZ
    @39
    clt
    wph
    @87
    cW
    cZ
    wph
    @82
    @85
    resqcld
    #
    @33
    @35
    wph
    @87
    @87
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
    @23
    @19
    @21
    cmul
    co
    #
    cdiv
    co
    #
    @18
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
    #
    cW
    clt
    wph
    @87
    @97
    @89
    wph
    @92
    @96
    wph
    @91
    crp
    wcel
    #
    c4
    cz
    wcel
    #
    @92
    crp
    wcel
    #
    wph
    cX
    @90
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
    #
    wph
    @58
    c2
    cz
    wcel
    #
    @90
    crp
    wcel
    wph
    @57
    @58
    @63
    @64
    simp2d
    #
    2z
    cK
    c2
    rpexpcl
    sylancl
    #
    rpmulcld
    #
    4z
    @91
    c4
    rpexpcl
    sylancl
    #
    wph
    @95
    wph
    @95
    wph
    @94
    @18
    wph
    @23
    @93
    wph
    @22
    crp
    wcel
    #
    cB
    crp
    wcel
    @23
    crp
    wcel
    @22
    cn
    wcel
    @108
    c3
    c2
    3nn0
    2nn
    decnncl
    @22
    nnrp
    ax-mp
    pntlem1.b
    @22
    cB
    rpmulcl
    sylancr
    #
    wph
    @19
    @21
    wph
    @60
    @61
    @62
    @78
    simp3d
    #
    wph
    cL
    @20
    @56
    wph
    @57
    @103
    @20
    crp
    wcel
    @65
    2z
    cE
    c2
    rpexpcl
    sylancl
    rpmulcld
    #
    rpmulcld
    #
    rpdivcld
    wph
    @17
    cC
    wph
    cU
    crp
    wcel
    c3
    crp
    wcel
    #
    @17
    crp
    wcel
    pntlem1.u
    c3
    cn
    wcel
    @113
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
    #
    rpmulcld
    rpred
    #
    rpefcld
    #
    rpaddcld
    #
    ltaddrpd
    pntlem1.w
    syl6breqr
    @36
    ltletrd
    wph
    @27
    cc0
    cZ
    cle
    wbr
    wa
    #
    @39
    cZ
    wceq
    wph
    cZ
    @37
    rprege0d
    #
    cZ
    resqrtth
    syl
    #
    breqtrrd
    wph
    @82
    cr
    wcel
    cc0
    @82
    cle
    wbr
    wa
    @2
    cr
    wcel
    cc0
    @2
    cle
    wbr
    wa
    #
    @86
    @88
    wb
    wph
    @82
    @84
    rprege0d
    wph
    @2
    @45
    rprege0d
    #
    @82
    @2
    lt2sq
    syl2anc
    mpbird
    #
    lttrd
    #
    lttrd
    lttrd
    #
    lttrd
    wph
    @42
    cc0
    c1
    cle
    wbr
    #
    @121
    @40
    @41
    wb
    @43
    @126
    wph
    0le1
    a1i
    @122
    c1
    @2
    lt2sq
    syl21anc
    mpbid
    @38
    c1
    wceq
    wph
    sq1
    a1i
    @120
    3brtr3d
    wph
    ceu
    @2
    @44
    @46
    @125
    ltled
    wph
    @2
    @4
    @46
    wph
    cZ
    cY
    @35
    @83
    rerpdivcld
    wph
    @2
    cY
    cmul
    co
    #
    cZ
    clt
    wbr
    @2
    @4
    clt
    wbr
    wph
    @127
    @2
    @2
    cmul
    co
    #
    cZ
    clt
    wph
    cY
    @2
    @2
    wph
    cY
    @83
    rpred
    #
    @46
    @45
    wph
    cY
    @82
    @2
    @129
    @85
    @46
    wph
    cY
    @7
    @129
    @67
    ltaddrpd
    @123
    lttrd
    ltmul2dd
    wph
    @118
    @128
    cZ
    wceq
    @119
    cZ
    remsqsqrt
    syl
    breqtrd
    wph
    @2
    cZ
    cY
    @46
    @35
    @83
    ltmuldivd
    mpbid
    ltled
    3jca
    wph
    @8
    @16
    @26
    wph
    @7
    @2
    @68
    @46
    @124
    ltled
    wph
    @12
    @15
    wph
    @11
    cr
    wcel
    c2
    cr
    wcel
    @12
    cr
    wcel
    wph
    @9
    @10
    wph
    cX
    @102
    relogcld
    #
    wph
    cK
    wph
    cK
    @104
    rpred
    wph
    @60
    @61
    @62
    @78
    simp2d
    rplogcld
    #
    rerpdivcld
    2re
    @11
    c2
    readdcl
    sylancl
    wph
    @14
    cr
    wcel
    @54
    @15
    cr
    wcel
    wph
    @13
    @10
    wph
    cZ
    @37
    relogcld
    #
    @131
    rerpdivcld
    4nn
    @14
    c4
    nndivre
    sylancl
    wph
    @91
    clog
    cfv
    #
    @10
    cdiv
    co
    #
    @13
    c4
    cdiv
    co
    #
    @10
    cdiv
    co
    #
    @12
    @15
    clt
    wph
    @133
    @135
    @10
    wph
    @91
    @106
    relogcld
    #
    wph
    @13
    cr
    wcel
    #
    @54
    @135
    cr
    wcel
    @132
    4nn
    @13
    c4
    nndivre
    sylancl
    @131
    wph
    c4
    @133
    cmul
    co
    #
    @13
    clt
    wbr
    #
    @133
    @135
    clt
    wbr
    #
    wph
    @92
    clog
    cfv
    #
    @139
    @13
    clt
    wph
    @99
    @100
    @142
    @139
    wceq
    @106
    4z
    @91
    c4
    relogexp
    sylancl
    wph
    @92
    cZ
    clt
    wbr
    #
    @142
    @13
    clt
    wbr
    #
    wph
    @92
    @97
    cZ
    wph
    @92
    @107
    rpred
    #
    wph
    @97
    @117
    rpred
    #
    @35
    wph
    @92
    @96
    @145
    @116
    ltaddrpd
    wph
    @97
    cW
    cZ
    @146
    @33
    @35
    wph
    @97
    @97
    @87
    caddc
    co
    #
    cW
    clt
    wph
    @97
    @87
    @146
    wph
    @82
    crp
    wcel
    @103
    @87
    crp
    wcel
    @84
    2z
    @82
    c2
    rpexpcl
    sylancl
    ltaddrpd
    wph
    cW
    @98
    @147
    pntlem1.w
    wph
    @87
    @97
    wph
    @87
    @89
    recnd
    wph
    @97
    @117
    rpcnd
    addcomd
    syl5eq
    breqtrrd
    @36
    ltletrd
    #
    lttrd
    wph
    @101
    @0
    @143
    @144
    wb
    @107
    @37
    @92
    cZ
    logltb
    syl2anc
    mpbid
    eqbrtrrd
    wph
    @133
    cr
    wcel
    @138
    @80
    @140
    @141
    wb
    @137
    @132
    @81
    @133
    @13
    c4
    ltmuldiv2
    syl3anc
    mpbid
    ltdiv1dd
    wph
    @134
    @9
    c2
    @10
    cmul
    co
    #
    caddc
    co
    #
    @10
    cdiv
    co
    #
    @11
    @149
    @10
    cdiv
    co
    #
    caddc
    co
    #
    @12
    wph
    @133
    @150
    @10
    cdiv
    wph
    @133
    @9
    @90
    clog
    cfv
    #
    caddc
    co
    @150
    wph
    cX
    @90
    @102
    @105
    relogmuld
    wph
    @154
    @149
    @9
    caddc
    wph
    @58
    @103
    @154
    @149
    wceq
    @104
    2z
    cK
    c2
    relogexp
    sylancl
    oveq2d
    eqtrd
    oveq1d
    wph
    @9
    cc
    wcel
    @149
    cc
    wcel
    @10
    cc
    wcel
    #
    @10
    cc0
    wne
    #
    wa
    #
    @151
    @153
    wceq
    wph
    @9
    @130
    recnd
    wph
    c2
    @10
    wph
    2cnd
    #
    wph
    @10
    @131
    rpcnd
    #
    mulcld
    wph
    @10
    @131
    rpcnne0d
    #
    @9
    @149
    @10
    divdir
    syl3anc
    wph
    @152
    c2
    @11
    caddc
    wph
    c2
    @10
    @158
    @159
    wph
    @155
    @156
    @160
    simprd
    divcan4d
    oveq2d
    3eqtrd
    wph
    @13
    cc
    wcel
    c4
    cc
    wcel
    c4
    cc0
    wne
    wa
    #
    @157
    @136
    @15
    wceq
    wph
    @13
    @132
    recnd
    @53
    @161
    wph
    @55
    c4
    rpcnne0
    mp1i
    @160
    @13
    c4
    @10
    divdiv32
    syl3anc
    3brtr3d
    ltled
    wph
    @18
    @93
    @23
    cdiv
    co
    #
    @13
    cmul
    co
    #
    @25
    cle
    wph
    @18
    @163
    wph
    @18
    @114
    rpred
    #
    wph
    @162
    @13
    wph
    @162
    wph
    @93
    @23
    @112
    @109
    rpdivcld
    #
    rpred
    @132
    remulcld
    wph
    @18
    @162
    cdiv
    co
    #
    @13
    clt
    wbr
    @18
    @163
    clt
    wbr
    wph
    @166
    @95
    @13
    clt
    wph
    @166
    @18
    @23
    cmul
    co
    #
    @93
    cdiv
    co
    #
    @23
    @18
    cmul
    co
    #
    @93
    cdiv
    co
    #
    @95
    wph
    @18
    cc
    wcel
    #
    @93
    cc
    wcel
    @93
    cc0
    wne
    wa
    #
    @23
    cc
    wcel
    #
    @23
    cc0
    wne
    wa
    #
    @166
    @168
    wceq
    wph
    @18
    @114
    rpcnd
    #
    wph
    @93
    @112
    rpcnne0d
    #
    wph
    @23
    @109
    rpcnne0d
    #
    @18
    @93
    @23
    divdiv2
    syl3anc
    wph
    @167
    @169
    @93
    cdiv
    wph
    @18
    @23
    @175
    wph
    @23
    @109
    rpcnd
    #
    mulcomd
    oveq1d
    wph
    @173
    @171
    @172
    @170
    @95
    wceq
    @178
    @175
    @176
    @23
    @18
    @93
    div23
    syl3anc
    3eqtrd
    wph
    @95
    @13
    clt
    wbr
    #
    @96
    @13
    ce
    cfv
    #
    clt
    wbr
    #
    wph
    @96
    cZ
    @180
    clt
    wph
    @96
    @97
    cZ
    wph
    @95
    @115
    reefcld
    #
    @146
    @35
    wph
    @96
    @92
    @182
    @107
    ltaddrp2d
    @148
    lttrd
    wph
    cZ
    @37
    reeflogd
    breqtrrd
    wph
    @95
    cr
    wcel
    @138
    @179
    @181
    wb
    @115
    @132
    @95
    @13
    eflt
    syl2anc
    mpbird
    eqbrtrd
    wph
    @18
    @13
    @162
    @164
    @132
    @165
    ltdivmuld
    mpbid
    ltled
    wph
    @162
    @24
    @13
    cmul
    wph
    @19
    cc
    wcel
    @21
    cc
    wcel
    @174
    @162
    @24
    wceq
    wph
    @19
    @110
    rpcnd
    wph
    @21
    @111
    rpcnd
    @177
    @19
    @21
    @23
    divass
    syl3anc
    oveq1d
    breqtrd
    3jca
    3jca
end
