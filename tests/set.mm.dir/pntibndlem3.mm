include "cv.mm"
include "cchp.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "clog.mm"
include "cdiv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "wral.mm"
include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "crp.mm"
include "wrex.mm"
include "clt.mm"
include "wa.mm"
include "cabs.mm"
include "ce.mm"
include "cico.mm"
include "cr.mm"
include "wcel.mm"
include "2re.mm"
include "1le2.mm"
include "chpdifbnd.mm"
include "mp2an.mm"
include "c4.mm"
include "simpr.mm"
include "cc0.mm"
include "ioossre.mm"
include "sseldi.mm"
include "eliooord.mm"
include "syl.mm"
include "simpld.mm"
include "elrpd.mm"
include "adantr.mm"
include "cn.mm"
include "4nn.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "rpdivcl.mm"
include "sylancl.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "rpefcld.mm"
include "rpaddcld.mm"
include "adantrr.mm"
include "elioore.mm"
include "ad2antll.mm"
include "reefcld.mm"
include "readdcld.mm"
include "ltaddrp2d.mm"
include "lttrd.mm"
include "cxr.mm"
include "wb.mm"
include "rexrd.mm"
include "elioopnf.mm"
include "mpbir2and.mm"
include "adantlrr.mm"
include "remulcl.mm"
include "sylancr.mm"
include "2rp.mm"
include "relogcl.mm"
include "readdcl.mm"
include "syl5eqel.mm"
include "rerpdivcld.mm"
include "elicopnf.mm"
include "simprbda.mm"
include "rehalfcld.mm"
include "rphalfcld.mm"
include "cc.mm"
include "wceq.mm"
include "recnd.mm"
include "recni.mm"
include "efadd.mm"
include "reeflog.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "a1i.mm"
include "rerpdivcl.mm"
include "div1i.mm"
include "simprd.mm"
include "wi.mm"
include "1re.mm"
include "ltle.mm"
include "mpd.mm"
include "rpregt0d.mm"
include "1rp.mm"
include "rpregt0.mm"
include "mp1i.mm"
include "1lt2.mm"
include "rplogcl.mm"
include "lediv2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "leadd2dd.mm"
include "oveq1i.mm"
include "wne.mm"
include "rpcnne0.mm"
include "divdir.mm"
include "syl5eq.mm"
include "mulcom.mm"
include "oveq1d.mm"
include "divdiv2.mm"
include "eqtr4d.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "efle.mm"
include "syl2anc.mm"
include "eqbrtrrd.mm"
include "simplbda.mm"
include "letrd.mm"
include "lemuldiv.mm"
include "syl5eqbr.mm"
include "ad2antrr.mm"
include "oveq1.mm"
include "breq2d.mm"
include "anbi2d.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "weq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "cbvrexv.mm"
include "oveq2.mm"
include "syl5bb.mm"
include "cbvralv.mm"
include "sylib.mm"
include "simprrl.mm"
include "simplrl.mm"
include "simplrr.mm"
include "eqid.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprrr.mm"
include "pntibndlem2.mm"
include "anassrs.mm"
include "rexlimddv.mm"
include "ralrimivva.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "rexlimdvaa.mm"
include "mpi.mm"

theorem pntibndlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let cE: class E
  let cK: class K
  let cL: class L
  let cZ: class Z
  let va: setvar a
  let vd: setvar d
  let vj: setvar j
  let vn: setvar n
  let vt: setvar t
  let vw: setvar w
  let cN: class N
  let vc: setvar c
  let ve: setvar e
  let cM: class M
  let cT: class T
  let cY: class Y
  assume pntibnd.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntibndlem1.1: |- ( ph -> A e. RR+ )
  assume pntibndlem1.l: |- L = ( ( 1 / 4 ) / ( A + 3 ) )
  assume pntibndlem3.2: |- ( ph -> A. x e. RR+ ( abs ` ( ( R ` x ) / x ) ) <_ A )
  assume pntibndlem3.3: |- ( ph -> B e. RR+ )
  assume pntibndlem3.k: |- K = ( exp ` ( B / ( E / 2 ) ) )
  assume pntibndlem3.c: |- C = ( ( 2 x. B ) + ( log ` 2 ) )
  assume pntibndlem3.4: |- ( ph -> E e. ( 0 (,) 1 ) )
  assume pntibndlem3.6: |- ( ph -> Z e. RR+ )
  assume pntibndlem3.5: |- ( ph -> A. m e. ( K [,) +oo ) A. v e. ( Z (,) +oo ) E. i e. NN ( ( v < i /\ i <_ ( m x. v ) ) /\ ( abs ` ( ( R ` i ) / i ) ) <_ ( E / 2 ) ) )

  disjoint a i
  disjoint a k
  disjoint a m
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint E a
  disjoint i k
  disjoint i m
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint E i
  disjoint k m
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint E k
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint E m
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint E u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint E v
  disjoint x y
  disjoint x z
  disjoint E x
  disjoint y z
  disjoint E y
  disjoint E z
  disjoint L u
  disjoint L v
  disjoint L x
  disjoint L z
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint C u
  disjoint C v
  disjoint C x
  disjoint C y
  disjoint R i
  disjoint R k
  disjoint R m
  disjoint R u
  disjoint R v
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint K m
  disjoint Z k
  disjoint Z m
  disjoint Z u
  disjoint Z v
  disjoint Z x
  disjoint Z y
  disjoint k ph
  disjoint ph u
  disjoint ph y
  disjoint a d
  disjoint a j
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint E d
  disjoint i j
  disjoint i n
  disjoint i t
  disjoint i w
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint E j
  disjoint k n
  disjoint k t
  disjoint k w
  disjoint m n
  disjoint m t
  disjoint m w
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint E n
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint E t
  disjoint u w
  disjoint v w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint E w
  disjoint L n
  disjoint L t
  disjoint N a
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint C n
  disjoint C t
  disjoint C w
  disjoint c d
  disjoint c e
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint d e
  disjoint R d
  disjoint e i
  disjoint e j
  disjoint e k
  disjoint e m
  disjoint e n
  disjoint e t
  disjoint e u
  disjoint e v
  disjoint e w
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint R e
  disjoint R j
  disjoint R n
  disjoint R t
  disjoint R w
  disjoint M z
  disjoint T x
  disjoint T y
  disjoint Y z
  disjoint Z n
  disjoint Z w
  disjoint n ph
  disjoint ph t
  disjoint ph w
  assert |- ( ph -> E. x e. RR+ A. k e. ( ( exp ` ( C / E ) ) [,) +oo ) A. y e. ( x (,) +oo ) E. z e. RR+ ( ( y < z /\ ( ( 1 + ( L x. E ) ) x. z ) < ( k x. y ) ) /\ A. u e. ( z [,] ( ( 1 + ( L x. E ) ) x. z ) ) ( abs ` ( ( R ` u ) / u ) ) <_ E ) )

  proof
    wph
    vw
    cv
    #
    cchp
    cfv
    vv
    cv
    #
    cchp
    cfv
    cmin
    co
    c2
    @0
    @1
    cmin
    co
    cmul
    co
    vt
    cv
    #
    @1
    @1
    clog
    cfv
    cdiv
    co
    cmul
    co
    caddc
    co
    cle
    wbr
    vw
    @1
    c2
    @1
    cmul
    co
    cicc
    co
    wral
    vv
    c1
    cpnf
    cioo
    co
    wral
    #
    vt
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
    c1
    cL
    cE
    cmul
    co
    caddc
    co
    @6
    cmul
    co
    #
    vk
    cv
    #
    @5
    cmul
    co
    clt
    wbr
    wa
    vu
    cv
    #
    cR
    cfv
    @9
    cdiv
    co
    cabs
    cfv
    cE
    cle
    wbr
    vu
    @6
    @7
    cicc
    co
    wral
    wa
    vz
    crp
    wrex
    #
    vy
    vx
    cv
    #
    cpnf
    cioo
    co
    #
    wral
    #
    vk
    cC
    cE
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
    c2
    cr
    wcel
    #
    c1
    c2
    cle
    wbr
    @4
    2re
    1le2
    vv
    vw
    c2
    vt
    chpdifbnd
    mp2an
    wph
    @3
    @18
    vt
    crp
    wph
    @2
    crp
    wcel
    #
    @3
    wa
    #
    wa
    #
    @2
    cE
    c4
    cdiv
    co
    #
    cdiv
    co
    #
    ce
    cfv
    #
    cZ
    caddc
    co
    #
    crp
    wcel
    #
    @10
    vy
    @26
    cpnf
    cioo
    co
    #
    wral
    #
    vk
    @16
    wral
    #
    @18
    wph
    @20
    @27
    @3
    wph
    @20
    wa
    #
    @25
    cZ
    @31
    @24
    @31
    @24
    @31
    @2
    @23
    wph
    @20
    simpr
    @31
    cE
    crp
    wcel
    #
    c4
    crp
    wcel
    #
    @23
    crp
    wcel
    wph
    @32
    @20
    wph
    cE
    wph
    cc0
    c1
    cioo
    co
    #
    cr
    cE
    cc0
    c1
    ioossre
    pntibndlem3.4
    sseldi
    #
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
    cE
    @34
    wcel
    #
    @36
    @37
    wa
    pntibndlem3.4
    cE
    cc0
    c1
    eliooord
    syl
    #
    simpld
    elrpd
    adantr
    #
    c4
    cn
    wcel
    @33
    4nn
    c4
    nnrp
    ax-mp
    cE
    c4
    rpdivcl
    sylancl
    rpdivcld
    rpred
    #
    rpefcld
    #
    wph
    cZ
    crp
    wcel
    #
    @20
    pntibndlem3.6
    adantr
    #
    rpaddcld
    adantrr
    @22
    @10
    vk
    vy
    @16
    @28
    @22
    @8
    @16
    wcel
    #
    @5
    @28
    wcel
    #
    wa
    #
    wa
    #
    @5
    vn
    cv
    #
    clt
    wbr
    #
    @49
    @8
    c2
    cdiv
    co
    #
    @5
    cmul
    co
    #
    cle
    wbr
    #
    wa
    #
    @49
    cR
    cfv
    #
    @49
    cdiv
    co
    #
    cabs
    cfv
    #
    cE
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    wa
    #
    @10
    vn
    cn
    @48
    @5
    cZ
    cpnf
    cioo
    co
    #
    wcel
    #
    @1
    vi
    cv
    #
    clt
    wbr
    #
    @63
    @51
    @1
    cmul
    co
    #
    cle
    wbr
    #
    wa
    #
    @63
    cR
    cfv
    #
    @63
    cdiv
    co
    #
    cabs
    cfv
    #
    @58
    cle
    wbr
    #
    wa
    #
    vi
    cn
    wrex
    #
    vv
    @61
    wral
    #
    @60
    vn
    cn
    wrex
    #
    wph
    @20
    @47
    @62
    @3
    @31
    @47
    wa
    #
    @62
    @5
    cr
    wcel
    #
    cZ
    @5
    clt
    wbr
    #
    @46
    @77
    @31
    @45
    @5
    @26
    cpnf
    elioore
    ad2antll
    #
    @76
    cZ
    @26
    @5
    @31
    cZ
    cr
    wcel
    @47
    @31
    cZ
    @44
    rpred
    #
    adantr
    #
    @31
    @26
    cr
    wcel
    @47
    @31
    @25
    cZ
    @31
    @24
    @41
    reefcld
    @80
    readdcld
    adantr
    @79
    @31
    cZ
    @26
    clt
    wbr
    @47
    @31
    cZ
    @25
    @80
    @42
    ltaddrp2d
    adantr
    @46
    @26
    @5
    clt
    wbr
    #
    @31
    @45
    @46
    @82
    @5
    cpnf
    clt
    wbr
    @5
    @26
    cpnf
    eliooord
    simpld
    ad2antll
    lttrd
    @76
    cZ
    cxr
    wcel
    @62
    @77
    @78
    wa
    wb
    @76
    cZ
    @81
    rexrd
    cZ
    @5
    elioopnf
    syl
    mpbir2and
    adantlrr
    @48
    @51
    cK
    cpnf
    cico
    co
    #
    wcel
    #
    @64
    @63
    vm
    cv
    #
    @1
    cmul
    co
    #
    cle
    wbr
    #
    wa
    #
    @71
    wa
    #
    vi
    cn
    wrex
    #
    vv
    @61
    wral
    #
    vm
    @83
    wral
    #
    @74
    wph
    @20
    @47
    @84
    @3
    @31
    @45
    @84
    @46
    @31
    @45
    wa
    #
    @84
    @51
    cr
    wcel
    #
    cK
    @51
    cle
    wbr
    #
    @93
    @8
    @31
    @45
    @8
    cr
    wcel
    #
    @15
    @8
    cle
    wbr
    #
    @31
    @15
    cr
    wcel
    #
    @45
    @96
    @97
    wa
    wb
    @31
    @14
    @31
    cC
    cE
    @31
    cC
    c2
    cB
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
    cr
    pntibndlem3.c
    @31
    @99
    cr
    wcel
    #
    @100
    cr
    wcel
    #
    @101
    cr
    wcel
    @31
    @19
    cB
    cr
    wcel
    @102
    2re
    @31
    cB
    wph
    cB
    crp
    wcel
    #
    @20
    pntibndlem3.3
    adantr
    rpred
    #
    c2
    cB
    remulcl
    sylancr
    #
    c2
    crp
    wcel
    #
    @103
    2rp
    c2
    relogcl
    ax-mp
    #
    @99
    @100
    readdcl
    sylancl
    syl5eqel
    @40
    rerpdivcld
    #
    reefcld
    #
    @15
    @8
    elicopnf
    syl
    #
    simprbda
    #
    rehalfcld
    @93
    cK
    cB
    @58
    cdiv
    co
    #
    ce
    cfv
    #
    @51
    cle
    pntibndlem3.k
    @93
    @114
    c2
    cmul
    co
    #
    @8
    cle
    wbr
    #
    @114
    @51
    cle
    wbr
    #
    @93
    @115
    @15
    @8
    @31
    @115
    cr
    wcel
    #
    @45
    @31
    @114
    cr
    wcel
    #
    @19
    @118
    @31
    @113
    @31
    cB
    @58
    @105
    @31
    cE
    @40
    rphalfcld
    rerpdivcld
    #
    reefcld
    #
    2re
    @114
    c2
    remulcl
    sylancl
    adantr
    @31
    @98
    @45
    @110
    adantr
    @112
    @31
    @115
    @15
    cle
    wbr
    @45
    @31
    @113
    @100
    caddc
    co
    #
    ce
    cfv
    #
    @115
    @15
    cle
    @31
    @123
    @114
    @100
    ce
    cfv
    #
    cmul
    co
    #
    @115
    @31
    @113
    cc
    wcel
    @100
    cc
    wcel
    #
    @123
    @125
    wceq
    @31
    @113
    @120
    recnd
    @100
    @108
    recni
    #
    @113
    @100
    efadd
    sylancl
    @124
    c2
    @114
    cmul
    @107
    @124
    c2
    wceq
    2rp
    c2
    reeflog
    ax-mp
    oveq2i
    syl6eq
    @31
    @122
    @14
    cle
    wbr
    #
    @123
    @15
    cle
    wbr
    #
    @31
    @122
    @113
    @100
    cE
    cdiv
    co
    #
    caddc
    co
    #
    @14
    cle
    @31
    @100
    @130
    @113
    @103
    @31
    @108
    a1i
    @31
    @103
    @32
    @130
    cr
    wcel
    @108
    @40
    @100
    cE
    rerpdivcl
    sylancr
    @120
    @31
    @100
    @100
    c1
    cdiv
    co
    #
    @130
    cle
    @100
    @127
    div1i
    @31
    cE
    c1
    cle
    wbr
    #
    @132
    @130
    cle
    wbr
    #
    @31
    @37
    @133
    wph
    @37
    @20
    wph
    @36
    @37
    @39
    simprd
    adantr
    @31
    cE
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @37
    @133
    wi
    wph
    @135
    @20
    @35
    adantr
    1re
    cE
    c1
    ltle
    sylancl
    mpd
    @31
    @135
    @36
    wa
    @136
    cc0
    c1
    clt
    wbr
    wa
    #
    @103
    cc0
    @100
    clt
    wbr
    wa
    #
    @133
    @134
    wb
    @31
    cE
    @40
    rpregt0d
    c1
    crp
    wcel
    @137
    @31
    1rp
    c1
    rpregt0
    mp1i
    @100
    crp
    wcel
    #
    @138
    @31
    @19
    c1
    c2
    clt
    wbr
    @139
    2re
    1lt2
    c2
    rplogcl
    mp2an
    @100
    rpregt0
    mp1i
    cE
    c1
    @100
    lediv2
    syl3anc
    mpbid
    syl5eqbrr
    leadd2dd
    @31
    @14
    @99
    cE
    cdiv
    co
    #
    @130
    caddc
    co
    #
    @131
    @31
    @14
    @101
    cE
    cdiv
    co
    #
    @141
    cC
    @101
    cE
    cdiv
    pntibndlem3.c
    oveq1i
    @31
    @99
    cc
    wcel
    @126
    cE
    cc
    wcel
    cE
    cc0
    wne
    wa
    #
    @142
    @141
    wceq
    @31
    @99
    @106
    recnd
    @126
    @31
    @127
    a1i
    @31
    @32
    @143
    @40
    cE
    rpcnne0
    syl
    #
    @99
    @100
    cE
    divdir
    syl3anc
    syl5eq
    @31
    @140
    @113
    @130
    caddc
    @31
    @140
    cB
    c2
    cmul
    co
    #
    cE
    cdiv
    co
    #
    @113
    @31
    @99
    @145
    cE
    cdiv
    @31
    c2
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @99
    @145
    wceq
    c2
    2re
    recni
    @31
    cB
    @105
    recnd
    #
    c2
    cB
    mulcom
    sylancr
    oveq1d
    @31
    @148
    @143
    @147
    c2
    cc0
    wne
    wa
    #
    @113
    @146
    wceq
    @149
    @144
    @107
    @150
    @31
    2rp
    c2
    rpcnne0
    mp1i
    cB
    cE
    c2
    divdiv2
    syl3anc
    eqtr4d
    oveq1d
    eqtrd
    breqtrrd
    @31
    @122
    cr
    wcel
    #
    @14
    cr
    wcel
    @128
    @129
    wb
    @31
    @113
    cr
    wcel
    @103
    @151
    @120
    @108
    @113
    @100
    readdcl
    sylancl
    @109
    @122
    @14
    efle
    syl2anc
    mpbid
    eqbrtrrd
    adantr
    @31
    @45
    @96
    @97
    @111
    simplbda
    letrd
    @93
    @119
    @96
    @19
    cc0
    c2
    clt
    wbr
    wa
    #
    @116
    @117
    wb
    @31
    @119
    @45
    @121
    adantr
    #
    @112
    @107
    @152
    @93
    2rp
    c2
    rpregt0
    mp1i
    @114
    @8
    c2
    lemuldiv
    syl3anc
    mpbid
    syl5eqbr
    @93
    cK
    cr
    wcel
    @84
    @94
    @95
    wa
    wb
    @93
    cK
    @114
    cr
    pntibndlem3.k
    @153
    syl5eqel
    cK
    @51
    elicopnf
    syl
    mpbir2and
    adantrr
    adantlrr
    wph
    @92
    @21
    @47
    pntibndlem3.5
    ad2antrr
    @91
    @74
    vm
    @51
    @83
    @85
    @51
    wceq
    #
    @90
    @73
    vv
    @61
    @154
    @89
    @72
    vi
    cn
    @154
    @88
    @67
    @71
    @154
    @87
    @66
    @64
    @154
    @86
    @65
    @63
    cle
    @85
    @51
    @1
    cmul
    oveq1
    breq2d
    anbi2d
    anbi1d
    rexbidv
    ralbidv
    rspcv
    sylc
    @73
    @75
    vv
    @5
    @61
    @73
    @1
    @49
    clt
    wbr
    #
    @49
    @65
    cle
    wbr
    #
    wa
    #
    @59
    wa
    #
    vn
    cn
    wrex
    vv
    vy
    weq
    #
    @75
    @72
    @158
    vi
    vn
    cn
    vi
    vn
    weq
    #
    @67
    @157
    @71
    @59
    @160
    @64
    @155
    @66
    @156
    @63
    @49
    @1
    clt
    breq2
    @63
    @49
    @65
    cle
    breq1
    anbi12d
    @160
    @70
    @57
    @58
    cle
    @160
    @69
    @56
    cabs
    @160
    @68
    @55
    @63
    @49
    cdiv
    @63
    @49
    cR
    fveq2
    @160
    id
    oveq12d
    fveq2d
    breq1d
    anbi12d
    cbvrexv
    @159
    @158
    @60
    vn
    cn
    @159
    @157
    @54
    @59
    @159
    @155
    @50
    @156
    @53
    @1
    @5
    @49
    clt
    breq1
    @159
    @65
    @52
    @49
    cle
    @1
    @5
    @51
    cmul
    oveq2
    breq2d
    anbi12d
    anbi1d
    rexbidv
    syl5bb
    rspcv
    sylc
    @22
    @47
    @49
    cn
    wcel
    #
    @60
    wa
    #
    @10
    @22
    @47
    @162
    wa
    #
    wa
    vv
    vw
    vz
    vu
    cA
    cB
    cC
    cR
    @2
    cE
    cK
    cL
    @8
    @49
    @26
    @5
    cZ
    va
    pntibnd.r
    wph
    cA
    crp
    wcel
    @21
    @163
    pntibndlem1.1
    ad2antrr
    pntibndlem1.l
    wph
    @1
    cR
    cfv
    #
    @1
    cdiv
    co
    #
    cabs
    cfv
    #
    cA
    cle
    wbr
    #
    vv
    crp
    wral
    #
    @21
    @163
    wph
    @11
    cR
    cfv
    #
    @11
    cdiv
    co
    #
    cabs
    cfv
    #
    cA
    cle
    wbr
    #
    vx
    crp
    wral
    @168
    pntibndlem3.2
    @172
    @167
    vx
    vv
    crp
    vx
    vv
    weq
    #
    @171
    @166
    cA
    cle
    @173
    @170
    @165
    cabs
    @173
    @169
    @164
    @11
    @1
    cdiv
    @11
    @1
    cR
    fveq2
    @173
    id
    oveq12d
    fveq2d
    breq1d
    cbvralv
    sylib
    ad2antrr
    wph
    @104
    @21
    @163
    pntibndlem3.3
    ad2antrr
    pntibndlem3.k
    pntibndlem3.c
    wph
    @38
    @21
    @163
    pntibndlem3.4
    ad2antrr
    wph
    @43
    @21
    @163
    pntibndlem3.6
    ad2antrr
    @22
    @47
    @161
    @60
    simprrl
    wph
    @20
    @3
    @163
    simplrl
    wph
    @20
    @3
    @163
    simplrr
    @26
    eqid
    @22
    @45
    @46
    @162
    simprll
    @22
    @45
    @46
    @162
    simprlr
    @22
    @47
    @161
    @60
    simprrr
    pntibndlem2
    anassrs
    rexlimddv
    ralrimivva
    @17
    @30
    vx
    @26
    crp
    @11
    @26
    wceq
    #
    @13
    @29
    vk
    @16
    @174
    @10
    vy
    @12
    @28
    @11
    @26
    cpnf
    cioo
    oveq1
    raleqdv
    ralbidv
    rspcev
    syl2anc
    rexlimdvaa
    mpi
end
