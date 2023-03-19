include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cle.mm"
include "wi.mm"
include "4sqlem16.mm"
include "simpld.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "wcel.mm"
include "cn.mm"
include "cv.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "wn.mm"
include "wne.mm"
include "c0.mm"
include "4sqlem13.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "sseldi.mm"
include "nnred.mm"
include "simprd.mm"
include "ltned.mm"
include "nncnd.mm"
include "sqvald.mm"
include "breq1d.mm"
include "cz.mm"
include "wb.mm"
include "nnzd.mm"
include "cprime.mm"
include "prmz.mm"
include "syl.mm"
include "nnne0d.mm"
include "dvdscmulr.mm"
include "syl112anc.mm"
include "dvdsprm.mm"
include "syl2anc.mm"
include "3bitrd.mm"
include "necon3bbid.mm"
include "mpbird.mm"
include "cn0.mm"
include "4sqlem14.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "orc.mm"
include "syl5.mm"
include "syld.mm"
include "mt3d.mm"
include "ci.mm"
include "caddc.mm"
include "cabs.mm"
include "cdiv.mm"
include "cre.mm"
include "cim.mm"
include "cgz.mm"
include "cc.mm"
include "gzreim.mm"
include "gzcn.mm"
include "absvalsq2d.mm"
include "zred.mm"
include "crred.mm"
include "oveq1d.mm"
include "crimd.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "prmnn.mm"
include "divcan3d.mm"
include "eqtr3d.mm"
include "cmin.mm"
include "4sqlem5.mm"
include "syl6eqr.mm"
include "mulcomd.mm"
include "eqid.mm"
include "zcnd.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "addsub4d.mm"
include "a1i.mm"
include "subdid.mm"
include "oveq2d.mm"
include "subcld.mm"
include "divdird.mm"
include "divassd.mm"
include "3eqtrd.mm"
include "eqeltrd.mm"
include "nnnn0d.mm"
include "mul4sqlem.mm"
include "eqeltrrd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "infssuzle.mm"
include "syl5eqbr.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "olcd.mm"
include "mpd.mm"
include "pm2.65i.mm"

theorem 4sqlem17
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vk: setvar k
  let vv: setvar v
  let vu: setvar u
  let vm: setvar m
  assume 4sq.1: |- S = { n | E. x e. ZZ E. y e. ZZ E. z e. ZZ E. w e. ZZ n = ( ( ( x ^ 2 ) + ( y ^ 2 ) ) + ( ( z ^ 2 ) + ( w ^ 2 ) ) ) }
  assume 4sq.2: |- ( ph -> N e. NN )
  assume 4sq.3: |- ( ph -> P = ( ( 2 x. N ) + 1 ) )
  assume 4sq.4: |- ( ph -> P e. Prime )
  assume 4sq.5: |- ( ph -> ( 0 ... ( 2 x. N ) ) C_ S )
  assume 4sq.6: |- T = { i e. NN | ( i x. P ) e. S }
  assume 4sq.7: |- M = inf ( T , RR , < )
  assume 4sq.m: |- ( ph -> M e. ( ZZ>= ` 2 ) )
  assume 4sq.a: |- ( ph -> A e. ZZ )
  assume 4sq.b: |- ( ph -> B e. ZZ )
  assume 4sq.c: |- ( ph -> C e. ZZ )
  assume 4sq.d: |- ( ph -> D e. ZZ )
  assume 4sq.e: |- E = ( ( ( A + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sq.f: |- F = ( ( ( B + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sq.g: |- G = ( ( ( C + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sq.h: |- H = ( ( ( D + ( M / 2 ) ) mod M ) - ( M / 2 ) )
  assume 4sq.r: |- R = ( ( ( ( E ^ 2 ) + ( F ^ 2 ) ) + ( ( G ^ 2 ) + ( H ^ 2 ) ) ) / M )
  assume 4sq.p: |- ( ph -> ( M x. P ) = ( ( ( A ^ 2 ) + ( B ^ 2 ) ) + ( ( C ^ 2 ) + ( D ^ 2 ) ) ) )

  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B n
  disjoint E n
  disjoint G n
  disjoint H n
  disjoint A n
  disjoint C n
  disjoint D n
  disjoint F n
  disjoint i n
  disjoint M i
  disjoint M n
  disjoint N n
  disjoint P i
  disjoint P n
  disjoint n ph
  disjoint S i
  disjoint S n
  disjoint R i
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a n
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b d
  disjoint b n
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c d
  disjoint c n
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d n
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint a j
  disjoint a k
  disjoint a v
  disjoint A a
  disjoint b j
  disjoint b k
  disjoint b v
  disjoint A b
  disjoint c j
  disjoint c k
  disjoint c v
  disjoint A c
  disjoint d j
  disjoint d k
  disjoint d v
  disjoint A d
  disjoint j k
  disjoint j n
  disjoint j v
  disjoint A j
  disjoint k n
  disjoint k v
  disjoint A k
  disjoint n v
  disjoint A v
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint F j
  disjoint a i
  disjoint a u
  disjoint M a
  disjoint b i
  disjoint b u
  disjoint M b
  disjoint c i
  disjoint c u
  disjoint M c
  disjoint d i
  disjoint d u
  disjoint M d
  disjoint i k
  disjoint i u
  disjoint k u
  disjoint M k
  disjoint n u
  disjoint M u
  disjoint k m
  disjoint N k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint N m
  disjoint u v
  disjoint N u
  disjoint N v
  disjoint a m
  disjoint P a
  disjoint b m
  disjoint P b
  disjoint c m
  disjoint P c
  disjoint d m
  disjoint P d
  disjoint i j
  disjoint i m
  disjoint i v
  disjoint j m
  disjoint j u
  disjoint P j
  disjoint P k
  disjoint P m
  disjoint P u
  disjoint P v
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph u
  disjoint ph v
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S u
  disjoint S v
  disjoint T k
  disjoint T u
  assert |- -. ph

  proof
    wph
    cM
    c2
    cexp
    co
    #
    cM
    cP
    cmul
    co
    #
    cdvds
    wbr
    #
    wph
    cR
    cc0
    wceq
    #
    cR
    cM
    wceq
    #
    wo
    #
    @2
    wph
    @4
    @3
    wph
    @4
    cR
    cM
    cle
    wbr
    #
    cM
    cR
    cle
    wbr
    wph
    @6
    @5
    @2
    wi
    #
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    cP
    cR
    cS
    cT
    vi
    vn
    cE
    cF
    cG
    cH
    cM
    cN
    4sq.1
    4sq.2
    4sq.3
    4sq.4
    4sq.5
    4sq.6
    4sq.7
    4sq.m
    4sq.a
    4sq.b
    4sq.c
    4sq.d
    4sq.e
    4sq.f
    4sq.g
    4sq.h
    4sq.r
    4sq.p
    4sqlem16
    #
    simpld
    wph
    cM
    cT
    cr
    clt
    cinf
    #
    cR
    cle
    4sq.7
    wph
    cT
    c1
    cuz
    cfv
    #
    wss
    #
    cR
    cT
    wcel
    #
    @9
    cR
    cle
    wbr
    cT
    cn
    @10
    cT
    vi
    cv
    #
    cP
    cmul
    co
    #
    cS
    wcel
    #
    vi
    cn
    crab
    cn
    4sq.6
    @15
    vi
    cn
    ssrab2
    eqsstri
    #
    nnuz
    sseqtri
    #
    wph
    cR
    cn
    wcel
    #
    cR
    cP
    cmul
    co
    #
    cS
    wcel
    #
    @12
    wph
    @18
    @2
    wph
    @2
    wn
    cM
    cP
    wne
    wph
    cM
    cP
    wph
    cM
    wph
    cT
    cn
    cM
    @16
    wph
    cM
    @9
    cT
    4sq.7
    wph
    @11
    cT
    c0
    wne
    #
    @9
    cT
    wcel
    @17
    wph
    @21
    cM
    cP
    clt
    wbr
    #
    wph
    vx
    vy
    vz
    vw
    cP
    cS
    cT
    vi
    vn
    cM
    cN
    4sq.1
    4sq.2
    4sq.3
    4sq.4
    4sq.5
    4sq.6
    4sq.7
    4sqlem13
    #
    simpld
    cT
    c1
    infssuzcl
    sylancr
    syl5eqel
    sseldi
    #
    nnred
    #
    wph
    @21
    @22
    @23
    simprd
    ltned
    wph
    @2
    cM
    cP
    wph
    @2
    cM
    cM
    cmul
    co
    #
    @1
    cdvds
    wbr
    #
    cM
    cP
    cdvds
    wbr
    #
    cM
    cP
    wceq
    #
    wph
    @0
    @26
    @1
    cdvds
    wph
    cM
    wph
    cM
    @24
    nncnd
    #
    sqvald
    breq1d
    wph
    cM
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    @31
    cM
    cc0
    wne
    @27
    @28
    wb
    wph
    cM
    @24
    nnzd
    #
    wph
    cP
    cprime
    wcel
    #
    @32
    4sq.4
    cP
    prmz
    syl
    @33
    wph
    cM
    @24
    nnne0d
    #
    cM
    cM
    cP
    dvdscmulr
    syl112anc
    wph
    cM
    c2
    cuz
    cfv
    wcel
    @34
    @28
    @29
    wb
    4sq.m
    4sq.4
    cP
    cM
    dvdsprm
    syl2anc
    3bitrd
    necon3bbid
    mpbird
    #
    wph
    @18
    wn
    @3
    @2
    wph
    @18
    @3
    wph
    cR
    cn0
    wcel
    @18
    @3
    wo
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    cP
    cR
    cS
    cT
    vi
    vn
    cE
    cF
    cG
    cH
    cM
    cN
    4sq.1
    4sq.2
    4sq.3
    4sq.4
    4sq.5
    4sq.6
    4sq.7
    4sq.m
    4sq.a
    4sq.b
    4sq.c
    4sq.d
    4sq.e
    4sq.f
    4sq.g
    4sq.h
    4sq.r
    4sq.p
    4sqlem14
    cR
    elnn0
    sylib
    ord
    @3
    @5
    wph
    @2
    @3
    @4
    orc
    wph
    @6
    @7
    @8
    simprd
    #
    syl5
    syld
    mt3d
    #
    wph
    cA
    ci
    cB
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    c2
    cexp
    co
    #
    cC
    ci
    cD
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    c2
    cexp
    co
    #
    caddc
    co
    #
    cM
    cdiv
    co
    #
    cE
    ci
    cF
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    c2
    cexp
    co
    #
    cG
    ci
    cH
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    c2
    cexp
    co
    #
    caddc
    co
    #
    cM
    cdiv
    co
    #
    cmul
    co
    #
    @19
    cS
    wph
    @55
    cP
    cR
    cmul
    co
    @19
    wph
    @46
    cP
    @54
    cR
    cmul
    wph
    @1
    cM
    cdiv
    co
    @46
    cP
    wph
    @1
    @45
    cM
    cdiv
    wph
    @1
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    cC
    c2
    cexp
    co
    #
    cD
    c2
    cexp
    co
    #
    caddc
    co
    #
    caddc
    co
    @45
    4sq.p
    wph
    @41
    @58
    @44
    @61
    caddc
    wph
    @41
    @40
    cre
    cfv
    #
    c2
    cexp
    co
    #
    @40
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    @58
    wph
    @40
    wph
    @40
    cgz
    wcel
    #
    @40
    cc
    wcel
    wph
    cA
    cz
    wcel
    cB
    cz
    wcel
    @66
    4sq.a
    4sq.b
    cA
    cB
    gzreim
    syl2anc
    #
    @40
    gzcn
    syl
    absvalsq2d
    wph
    @63
    @56
    @65
    @57
    caddc
    wph
    @62
    cA
    c2
    cexp
    wph
    cA
    cB
    wph
    cA
    4sq.a
    zred
    #
    wph
    cB
    4sq.b
    zred
    #
    crred
    oveq1d
    wph
    @64
    cB
    c2
    cexp
    wph
    cA
    cB
    @68
    @69
    crimd
    oveq1d
    oveq12d
    eqtrd
    wph
    @44
    @43
    cre
    cfv
    #
    c2
    cexp
    co
    #
    @43
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    @61
    wph
    @43
    wph
    @43
    cgz
    wcel
    #
    @43
    cc
    wcel
    wph
    cC
    cz
    wcel
    cD
    cz
    wcel
    @74
    4sq.c
    4sq.d
    cC
    cD
    gzreim
    syl2anc
    #
    @43
    gzcn
    syl
    absvalsq2d
    wph
    @71
    @59
    @73
    @60
    caddc
    wph
    @70
    cC
    c2
    cexp
    wph
    cC
    cD
    wph
    cC
    4sq.c
    zred
    #
    wph
    cD
    4sq.d
    zred
    #
    crred
    oveq1d
    wph
    @72
    cD
    c2
    cexp
    wph
    cC
    cD
    @76
    @77
    crimd
    oveq1d
    oveq12d
    eqtrd
    oveq12d
    eqtr4d
    oveq1d
    wph
    cP
    cM
    wph
    cP
    wph
    @34
    cP
    cn
    wcel
    4sq.4
    cP
    prmnn
    syl
    #
    nncnd
    #
    @30
    @35
    divcan3d
    eqtr3d
    #
    wph
    @54
    cE
    c2
    cexp
    co
    #
    cF
    c2
    cexp
    co
    #
    caddc
    co
    #
    cG
    c2
    cexp
    co
    #
    cH
    c2
    cexp
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    cM
    cdiv
    co
    cR
    wph
    @53
    @87
    cM
    cdiv
    wph
    @49
    @83
    @52
    @86
    caddc
    wph
    @49
    @48
    cre
    cfv
    #
    c2
    cexp
    co
    #
    @48
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    @83
    wph
    @48
    wph
    @48
    cgz
    wcel
    #
    @48
    cc
    wcel
    wph
    cE
    cz
    wcel
    #
    cF
    cz
    wcel
    #
    @92
    wph
    @93
    cA
    cE
    cmin
    co
    #
    cM
    cdiv
    co
    #
    cz
    wcel
    #
    wph
    cA
    cE
    cM
    4sq.a
    @24
    4sq.e
    4sqlem5
    #
    simpld
    #
    wph
    @94
    cB
    cF
    cmin
    co
    #
    cM
    cdiv
    co
    #
    cz
    wcel
    #
    wph
    cB
    cF
    cM
    4sq.b
    @24
    4sq.f
    4sqlem5
    #
    simpld
    #
    cE
    cF
    gzreim
    syl2anc
    #
    @48
    gzcn
    syl
    absvalsq2d
    wph
    @89
    @81
    @91
    @82
    caddc
    wph
    @88
    cE
    c2
    cexp
    wph
    cE
    cF
    wph
    cE
    @99
    zred
    #
    wph
    cF
    @104
    zred
    #
    crred
    oveq1d
    wph
    @90
    cF
    c2
    cexp
    wph
    cE
    cF
    @106
    @107
    crimd
    oveq1d
    oveq12d
    eqtrd
    wph
    @52
    @51
    cre
    cfv
    #
    c2
    cexp
    co
    #
    @51
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    @86
    wph
    @51
    wph
    @51
    cgz
    wcel
    #
    @51
    cc
    wcel
    wph
    cG
    cz
    wcel
    #
    cH
    cz
    wcel
    #
    @112
    wph
    @113
    cC
    cG
    cmin
    co
    #
    cM
    cdiv
    co
    #
    cz
    wcel
    #
    wph
    cC
    cG
    cM
    4sq.c
    @24
    4sq.g
    4sqlem5
    #
    simpld
    #
    wph
    @114
    cD
    cH
    cmin
    co
    #
    cM
    cdiv
    co
    #
    cz
    wcel
    #
    wph
    cD
    cH
    cM
    4sq.d
    @24
    4sq.h
    4sqlem5
    #
    simpld
    #
    cG
    cH
    gzreim
    syl2anc
    #
    @51
    gzcn
    syl
    absvalsq2d
    wph
    @109
    @84
    @111
    @85
    caddc
    wph
    @108
    cG
    c2
    cexp
    wph
    cG
    cH
    wph
    cG
    @119
    zred
    #
    wph
    cH
    @124
    zred
    #
    crred
    oveq1d
    wph
    @110
    cH
    c2
    cexp
    wph
    cG
    cH
    @126
    @127
    crimd
    oveq1d
    oveq12d
    eqtrd
    oveq12d
    oveq1d
    4sq.r
    syl6eqr
    oveq12d
    wph
    cP
    cR
    @79
    wph
    cR
    @38
    nncnd
    mulcomd
    eqtrd
    wph
    vx
    vy
    vz
    vw
    @40
    @43
    @48
    @51
    cS
    vn
    cM
    @45
    @53
    4sq.1
    @67
    @75
    @105
    @125
    @45
    eqid
    @53
    eqid
    @24
    wph
    @40
    @48
    cmin
    co
    #
    cM
    cdiv
    co
    #
    @96
    ci
    @101
    cmul
    co
    #
    caddc
    co
    #
    cgz
    wph
    @129
    @95
    ci
    @100
    cmul
    co
    #
    caddc
    co
    #
    cM
    cdiv
    co
    @96
    @132
    cM
    cdiv
    co
    #
    caddc
    co
    @131
    wph
    @128
    @133
    cM
    cdiv
    wph
    @128
    @95
    @39
    @47
    cmin
    co
    #
    caddc
    co
    @133
    wph
    cA
    @39
    cE
    @47
    wph
    cA
    4sq.a
    zcnd
    #
    wph
    ci
    cc
    wcel
    #
    cB
    cc
    wcel
    @39
    cc
    wcel
    ax-icn
    wph
    cB
    4sq.b
    zcnd
    #
    ci
    cB
    mulcl
    sylancr
    wph
    cE
    @99
    zcnd
    #
    wph
    @137
    cF
    cc
    wcel
    @47
    cc
    wcel
    ax-icn
    wph
    cF
    @104
    zcnd
    #
    ci
    cF
    mulcl
    sylancr
    addsub4d
    wph
    @132
    @135
    @95
    caddc
    wph
    ci
    cB
    cF
    @137
    wph
    ax-icn
    a1i
    #
    @138
    @140
    subdid
    oveq2d
    eqtr4d
    oveq1d
    wph
    @95
    @132
    cM
    wph
    cA
    cE
    @136
    @139
    subcld
    wph
    @137
    @100
    cc
    wcel
    @132
    cc
    wcel
    ax-icn
    wph
    cB
    cF
    @138
    @140
    subcld
    #
    ci
    @100
    mulcl
    sylancr
    @30
    @35
    divdird
    wph
    @134
    @130
    @96
    caddc
    wph
    ci
    @100
    cM
    @141
    @142
    @30
    @35
    divassd
    oveq2d
    3eqtrd
    wph
    @97
    @102
    @131
    cgz
    wcel
    wph
    @93
    @97
    @98
    simprd
    wph
    @94
    @102
    @103
    simprd
    @96
    @101
    gzreim
    syl2anc
    eqeltrd
    wph
    @43
    @51
    cmin
    co
    #
    cM
    cdiv
    co
    #
    @116
    ci
    @121
    cmul
    co
    #
    caddc
    co
    #
    cgz
    wph
    @144
    @115
    ci
    @120
    cmul
    co
    #
    caddc
    co
    #
    cM
    cdiv
    co
    @116
    @147
    cM
    cdiv
    co
    #
    caddc
    co
    @146
    wph
    @143
    @148
    cM
    cdiv
    wph
    @143
    @115
    @42
    @50
    cmin
    co
    #
    caddc
    co
    @148
    wph
    cC
    @42
    cG
    @50
    wph
    cC
    4sq.c
    zcnd
    #
    wph
    @137
    cD
    cc
    wcel
    @42
    cc
    wcel
    ax-icn
    wph
    cD
    4sq.d
    zcnd
    #
    ci
    cD
    mulcl
    sylancr
    wph
    cG
    @119
    zcnd
    #
    wph
    @137
    cH
    cc
    wcel
    @50
    cc
    wcel
    ax-icn
    wph
    cH
    @124
    zcnd
    #
    ci
    cH
    mulcl
    sylancr
    addsub4d
    wph
    @147
    @150
    @115
    caddc
    wph
    ci
    cD
    cH
    @141
    @152
    @154
    subdid
    oveq2d
    eqtr4d
    oveq1d
    wph
    @115
    @147
    cM
    wph
    cC
    cG
    @151
    @153
    subcld
    wph
    @137
    @120
    cc
    wcel
    @147
    cc
    wcel
    ax-icn
    wph
    cD
    cH
    @152
    @154
    subcld
    #
    ci
    @120
    mulcl
    sylancr
    @30
    @35
    divdird
    wph
    @149
    @145
    @116
    caddc
    wph
    ci
    @120
    cM
    @141
    @155
    @30
    @35
    divassd
    oveq2d
    3eqtrd
    wph
    @117
    @122
    @146
    cgz
    wcel
    wph
    @113
    @117
    @118
    simprd
    wph
    @114
    @122
    @123
    simprd
    @116
    @121
    gzreim
    syl2anc
    eqeltrd
    wph
    @46
    cP
    cn0
    @80
    wph
    cP
    @78
    nnnn0d
    eqeltrd
    mul4sqlem
    eqeltrrd
    @15
    @20
    vi
    cR
    cn
    cT
    @13
    cR
    wceq
    @14
    @19
    cS
    @13
    cR
    cP
    cmul
    oveq1
    eleq1d
    4sq.6
    elrab2
    sylanbrc
    cR
    cT
    c1
    infssuzle
    sylancr
    syl5eqbr
    wph
    cR
    cM
    wph
    cR
    @38
    nnred
    @25
    letri3d
    mpbir2and
    olcd
    @37
    mpd
    @36
    pm2.65i
end
