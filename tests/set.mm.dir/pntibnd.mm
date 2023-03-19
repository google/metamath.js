include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "crp.mm"
include "wral.mm"
include "wrex.mm"
include "clt.mm"
include "cmul.mm"
include "wa.mm"
include "cn.mm"
include "cpnf.mm"
include "cioo.mm"
include "ce.mm"
include "cico.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "cicc.mm"
include "pntrmax.mm"
include "pntpbnd.mm"
include "reeanv.mm"
include "wcel.mm"
include "c2.mm"
include "clog.mm"
include "c4.mm"
include "c3.mm"
include "2rp.mm"
include "rpmulcl.mm"
include "mpan.mm"
include "cr.mm"
include "2re.mm"
include "1lt2.mm"
include "rplogcl.mm"
include "mp2an.mm"
include "rpaddcl.mm"
include "sylancl.mm"
include "ad2antlr.mm"
include "id.mm"
include "eqid.mm"
include "pntibndlem1.mm"
include "ad2antrr.mm"
include "wi.mm"
include "elioore.mm"
include "eliooord.mm"
include "simpld.mm"
include "elrpd.mm"
include "rphalfcld.mm"
include "rpred.mm"
include "rpgt0d.mm"
include "1red.mm"
include "rphalflt.mm"
include "syl.mm"
include "simprd.mm"
include "lttrd.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "1re.mm"
include "rexri.mm"
include "elioo2.mm"
include "syl3anbrc.mm"
include "adantl.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "breq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "raleqbidv.mm"
include "rspcv.mm"
include "simp-4l.mm"
include "simpllr.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "pntibndlem3.mm"
include "rexlimdvaa.mm"
include "syld.mm"
include "ralrimdva.mm"
include "impr.mm"
include "oveq1.mm"
include "raleqdv.mm"
include "oveq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "rexralbidv.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "ex.mm"
include "rexlimivv.mm"
include "sylbir.mm"

theorem pntibnd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cR: class R
  let ve: setvar e
  let vk: setvar k
  let va: setvar a
  let vc: setvar c
  let vl: setvar l
  let cC: class C
  let cF: class F
  let vw: setvar w
  let cI: class I
  let vn: setvar n
  let cJ: class J
  let vj: setvar j
  let vm: setvar m
  let cL: class L
  let cK: class K
  let cM: class M
  let cO: class O
  let vv: setvar v
  let wph: wff ph
  let cN: class N
  let vb: setvar b
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let cV: class V
  let cU: class U
  let cW: class W
  let cX: class X
  let cY: class Y
  let cE: class E
  let cZ: class Z
  assume pntlem1.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )

  disjoint x z
  disjoint x y
  disjoint y z
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint c e
  disjoint c k
  disjoint c l
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint e k
  disjoint e l
  disjoint e u
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint R e
  disjoint k l
  disjoint R k
  disjoint l u
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint R l
  disjoint R u
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint a e
  disjoint a k
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C x
  disjoint C z
  disjoint F w
  disjoint I n
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint J n
  disjoint J x
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
  disjoint L k
  disjoint m n
  disjoint m u
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint L m
  disjoint n u
  disjoint L n
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
  disjoint c f
  disjoint c g
  disjoint c i
  disjoint c j
  disjoint c m
  disjoint c n
  disjoint c v
  disjoint c w
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
  disjoint e m
  disjoint e n
  disjoint e v
  disjoint e w
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
  disjoint k v
  disjoint k w
  disjoint l m
  disjoint l n
  disjoint l v
  disjoint l w
  disjoint m w
  disjoint R m
  disjoint n w
  disjoint R n
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
  disjoint a g
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a v
  disjoint E a
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
  assert |- E. c e. RR+ E. l e. ( 0 (,) 1 ) A. e e. ( 0 (,) 1 ) E. x e. RR+ A. k e. ( ( exp ` ( c / e ) ) [,) +oo ) A. y e. ( x (,) +oo ) E. z e. RR+ ( ( y < z /\ ( ( 1 + ( l x. e ) ) x. z ) < ( k x. y ) ) /\ A. u e. ( z [,] ( ( 1 + ( l x. e ) ) x. z ) ) ( abs ` ( ( R ` u ) / u ) ) <_ e )

  proof
    vx
    cv
    #
    cR
    cfv
    @0
    cdiv
    co
    cabs
    cfv
    vd
    cv
    #
    cle
    wbr
    vx
    crp
    wral
    #
    vd
    crp
    wrex
    #
    vv
    cv
    #
    vn
    cv
    #
    clt
    wbr
    @5
    vm
    cv
    @4
    cmul
    co
    cle
    wbr
    wa
    #
    @5
    cR
    cfv
    @5
    cdiv
    co
    cabs
    cfv
    #
    vf
    cv
    #
    cle
    wbr
    #
    wa
    #
    vn
    cn
    wrex
    #
    vv
    vg
    cv
    #
    cpnf
    cioo
    co
    #
    wral
    #
    vm
    vb
    cv
    #
    @8
    cdiv
    co
    #
    ce
    cfv
    #
    cpnf
    cico
    co
    #
    wral
    #
    vg
    crp
    wrex
    #
    vf
    cc0
    c1
    cioo
    co
    #
    wral
    #
    vb
    crp
    wrex
    #
    vy
    cv
    #
    vz
    cv
    #
    clt
    wbr
    #
    c1
    vl
    cv
    #
    ve
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    @25
    cmul
    co
    #
    vk
    cv
    @24
    cmul
    co
    #
    clt
    wbr
    #
    wa
    #
    vu
    cv
    #
    cR
    cfv
    @35
    cdiv
    co
    cabs
    cfv
    @28
    cle
    wbr
    #
    vu
    @25
    @31
    cicc
    co
    #
    wral
    #
    wa
    #
    vz
    crp
    wrex
    #
    vy
    @0
    cpnf
    cioo
    co
    #
    wral
    #
    vk
    vc
    cv
    #
    @28
    cdiv
    co
    #
    ce
    cfv
    #
    cpnf
    cico
    co
    #
    wral
    #
    vx
    crp
    wrex
    #
    ve
    @21
    wral
    #
    vl
    @21
    wrex
    vc
    crp
    wrex
    #
    vx
    cR
    va
    vd
    pntlem1.r
    pntrmax
    vg
    vv
    cR
    vf
    vm
    vn
    va
    vb
    pntlem1.r
    pntpbnd
    @3
    @23
    wa
    @2
    @22
    wa
    #
    vb
    crp
    wrex
    vd
    crp
    wrex
    @50
    @2
    @22
    vd
    vb
    crp
    crp
    reeanv
    @51
    @50
    vd
    vb
    crp
    crp
    @1
    crp
    wcel
    #
    @15
    crp
    wcel
    #
    wa
    #
    @51
    @50
    @54
    @51
    wa
    c2
    @15
    cmul
    co
    #
    c2
    clog
    cfv
    #
    caddc
    co
    #
    crp
    wcel
    #
    c1
    c4
    cdiv
    co
    @1
    c3
    caddc
    co
    cdiv
    co
    #
    @21
    wcel
    #
    @26
    c1
    @59
    @28
    cmul
    co
    #
    caddc
    co
    #
    @25
    cmul
    co
    #
    @32
    clt
    wbr
    #
    wa
    #
    @36
    vu
    @25
    @63
    cicc
    co
    #
    wral
    #
    wa
    #
    vz
    crp
    wrex
    #
    vy
    @41
    wral
    #
    vk
    @57
    @28
    cdiv
    co
    #
    ce
    cfv
    #
    cpnf
    cico
    co
    #
    wral
    vx
    crp
    wrex
    #
    ve
    @21
    wral
    #
    @50
    @53
    @58
    @52
    @51
    @53
    @55
    crp
    wcel
    #
    @56
    crp
    wcel
    #
    @58
    c2
    crp
    wcel
    @53
    @76
    2rp
    c2
    @15
    rpmulcl
    mpan
    c2
    cr
    wcel
    c1
    c2
    clt
    wbr
    @77
    2re
    1lt2
    c2
    rplogcl
    mp2an
    @55
    @56
    rpaddcl
    sylancl
    ad2antlr
    @52
    @60
    @53
    @51
    @52
    @1
    cR
    @59
    va
    pntlem1.r
    @52
    id
    @59
    eqid
    #
    pntibndlem1
    ad2antrr
    @54
    @2
    @22
    @75
    @54
    @2
    wa
    #
    @22
    @74
    ve
    @21
    @79
    @28
    @21
    wcel
    #
    wa
    #
    @22
    @6
    @7
    @28
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    wa
    #
    vn
    cn
    wrex
    #
    vv
    @13
    wral
    #
    vm
    @15
    @82
    cdiv
    co
    #
    ce
    cfv
    #
    cpnf
    cico
    co
    #
    wral
    #
    vg
    crp
    wrex
    #
    @74
    @81
    @82
    @21
    wcel
    #
    @22
    @91
    wi
    @80
    @92
    @79
    @80
    @82
    cr
    wcel
    #
    cc0
    @82
    clt
    wbr
    #
    @82
    c1
    clt
    wbr
    #
    @92
    @80
    @82
    @80
    @28
    @80
    @28
    @28
    cc0
    c1
    elioore
    #
    @80
    cc0
    @28
    clt
    wbr
    #
    @28
    c1
    clt
    wbr
    #
    @28
    cc0
    c1
    eliooord
    #
    simpld
    elrpd
    #
    rphalfcld
    #
    rpred
    #
    @80
    @82
    @101
    rpgt0d
    @80
    @82
    @28
    c1
    @102
    @96
    @80
    1red
    @80
    @28
    crp
    wcel
    @82
    @28
    clt
    wbr
    @100
    @28
    rphalflt
    syl
    @80
    @97
    @98
    @99
    simprd
    lttrd
    cc0
    cxr
    wcel
    c1
    cxr
    wcel
    @92
    @93
    @94
    @95
    w3a
    wb
    0xr
    c1
    1re
    rexri
    cc0
    c1
    @82
    elioo2
    mp2an
    syl3anbrc
    adantl
    @20
    @91
    vf
    @82
    @21
    @8
    @82
    wceq
    #
    @19
    @90
    vg
    crp
    @103
    @14
    @86
    vm
    @18
    @89
    @103
    @17
    @88
    cpnf
    cico
    @103
    @16
    @87
    ce
    @8
    @82
    @15
    cdiv
    oveq2
    fveq2d
    oveq1d
    @103
    @11
    @85
    vv
    @13
    @103
    @10
    @84
    vn
    cn
    @103
    @9
    @83
    @6
    @8
    @82
    @7
    cle
    breq2
    anbi2d
    rexbidv
    ralbidv
    raleqbidv
    rexbidv
    rspcv
    syl
    @81
    @90
    @74
    vg
    crp
    @81
    @12
    crp
    wcel
    #
    @90
    wa
    #
    wa
    vx
    vy
    vz
    vv
    vu
    @1
    @15
    @57
    cR
    vn
    vk
    vm
    @28
    @88
    @59
    @12
    va
    pntlem1.r
    @52
    @53
    @2
    @80
    @105
    simp-4l
    @78
    @54
    @2
    @80
    @105
    simpllr
    @79
    @53
    @80
    @105
    @52
    @53
    @2
    simplr
    ad2antrr
    @88
    eqid
    @57
    eqid
    @79
    @80
    @105
    simplr
    @81
    @104
    @90
    simprl
    @81
    @104
    @90
    simprr
    pntibndlem3
    rexlimdvaa
    syld
    ralrimdva
    impr
    @49
    @75
    @42
    vk
    @73
    wral
    #
    vx
    crp
    wrex
    #
    ve
    @21
    wral
    vc
    vl
    @57
    @59
    crp
    @21
    @43
    @57
    wceq
    #
    @48
    @107
    ve
    @21
    @108
    @47
    @106
    vx
    crp
    @108
    @42
    vk
    @46
    @73
    @108
    @45
    @72
    cpnf
    cico
    @108
    @44
    @71
    ce
    @43
    @57
    @28
    cdiv
    oveq1
    fveq2d
    oveq1d
    raleqdv
    rexbidv
    ralbidv
    @27
    @59
    wceq
    #
    @107
    @74
    ve
    @21
    @109
    @42
    @70
    vx
    vk
    crp
    @73
    @109
    @40
    @69
    vy
    @41
    @109
    @39
    @68
    vz
    crp
    @109
    @34
    @65
    @38
    @67
    @109
    @33
    @64
    @26
    @109
    @31
    @63
    @32
    clt
    @109
    @30
    @62
    @25
    cmul
    @109
    @29
    @61
    c1
    caddc
    @27
    @59
    @28
    cmul
    oveq1
    oveq2d
    oveq1d
    #
    breq1d
    anbi2d
    @109
    @36
    vu
    @37
    @66
    @109
    @31
    @63
    @25
    cicc
    @110
    oveq2d
    raleqdv
    anbi12d
    rexbidv
    ralbidv
    rexralbidv
    ralbidv
    rspc2ev
    syl3anc
    ex
    rexlimivv
    sylbir
    mp2an
end
