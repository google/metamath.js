include "c1.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wn.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "1re.mm"
include "cq.mm"
include "cn.mm"
include "c2.mm"
include "cuz.mm"
include "wa.mm"
include "eluz2b2.mm"
include "sylib.mm"
include "simpld.mm"
include "nnq.mm"
include "syl.mm"
include "qrngbas.mm"
include "abvcl.mm"
include "syl2anc.mm"
include "ltnle.mm"
include "sylancr.mm"
include "mpbid.mm"
include "ccxp.mm"
include "co.mm"
include "cmul.mm"
include "cdiv.mm"
include "caddc.mm"
include "cif.mm"
include "ifcl.mm"
include "syl5eqel.mm"
include "cc0.mm"
include "0red.mm"
include "a1i.mm"
include "0lt1.mm"
include "max2.mm"
include "sylancl.mm"
include "syl6breqr.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "clog.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "nnred.mm"
include "simprd.mm"
include "rplogcld.mm"
include "rerpdivcld.mm"
include "rpcxpcld.mm"
include "remulcld.mm"
include "peano2re.mm"
include "cv.mm"
include "ostth2lem3.mm"
include "ostth2lem1.mm"
include "ledivmuld.mm"
include "rpcnd.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "adantr.mm"
include "iftrue.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "recnd.mm"
include "1cxpd.mm"
include "sylan9eqr.mm"
include "mtand.mm"
include "mpbird.mm"
include "ce.mm"
include "lttrd.mm"
include "reeflogd.mm"
include "wceq.mm"
include "iffalse.mm"
include "rpne0d.mm"
include "cxpefd.mm"
include "eqtr2d.mm"
include "3brtr4d.mm"
include "efle.mm"
include "div12d.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "3brtr4g.mm"
include "jca.mm"

theorem ostth2lem4
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let vq: setvar q
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let cX: class X
  let cY: class Y
  let cP: class P
  assume qrng.q: |- Q = ( CCfld |`s QQ )
  assume qabsabv.a: |- A = ( AbsVal ` Q )
  assume padic.j: |- J = ( q e. Prime |-> ( x e. QQ |-> if ( x = 0 , 0 , ( q ^ -u ( q pCnt x ) ) ) ) )
  assume ostth.k: |- K = ( x e. QQ |-> if ( x = 0 , 0 , 1 ) )
  assume ostth.1: |- ( ph -> F e. A )
  assume ostth2.2: |- ( ph -> N e. ( ZZ>= ` 2 ) )
  assume ostth2.3: |- ( ph -> 1 < ( F ` N ) )
  assume ostth2.4: |- R = ( ( log ` ( F ` N ) ) / ( log ` N ) )
  assume ostth2.5: |- ( ph -> M e. ( ZZ>= ` 2 ) )
  assume ostth2.6: |- S = ( ( log ` ( F ` M ) ) / ( log ` M ) )
  assume ostth2.7: |- T = if ( ( F ` M ) <_ 1 , 1 , ( F ` M ) )
  assume ostth2.8: |- U = ( ( log ` N ) / ( log ` M ) )

  disjoint M x
  disjoint q x
  disjoint ph q
  disjoint ph x
  disjoint T x
  disjoint U x
  disjoint A q
  disjoint A x
  disjoint N x
  disjoint Q x
  disjoint F q
  disjoint R q
  disjoint F x
  disjoint k n
  disjoint k p
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint n p
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint p y
  disjoint p z
  disjoint G p
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint K k
  disjoint K n
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint M j
  disjoint k x
  disjoint M k
  disjoint n x
  disjoint M n
  disjoint a b
  disjoint a k
  disjoint a n
  disjoint a p
  disjoint a q
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint b k
  disjoint b n
  disjoint b p
  disjoint b q
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b ph
  disjoint k q
  disjoint k ph
  disjoint n q
  disjoint n ph
  disjoint p q
  disjoint p x
  disjoint p ph
  disjoint q y
  disjoint q z
  disjoint x y
  disjoint x z
  disjoint ph y
  disjoint ph z
  disjoint a g
  disjoint J a
  disjoint g p
  disjoint g y
  disjoint g z
  disjoint J g
  disjoint J p
  disjoint J y
  disjoint J z
  disjoint S a
  disjoint S b
  disjoint S k
  disjoint T j
  disjoint T k
  disjoint T n
  disjoint U n
  disjoint X k
  disjoint X x
  disjoint A a
  disjoint A k
  disjoint A n
  disjoint A p
  disjoint A y
  disjoint A z
  disjoint N k
  disjoint N n
  disjoint N y
  disjoint N z
  disjoint Q k
  disjoint Q n
  disjoint Q y
  disjoint Q z
  disjoint Y k
  disjoint a j
  disjoint F a
  disjoint b g
  disjoint b j
  disjoint F b
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint g q
  disjoint F g
  disjoint j p
  disjoint j q
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint F p
  disjoint F y
  disjoint F z
  disjoint P a
  disjoint P b
  disjoint P k
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint R a
  disjoint R p
  disjoint R y
  disjoint R z
  assert |- ( ph -> ( 1 < ( F ` M ) /\ R <_ S ) )

  proof
    wph
    c1
    cM
    cF
    cfv
    #
    clt
    wbr
    #
    cR
    cS
    cle
    wbr
    wph
    @1
    @0
    c1
    cle
    wbr
    #
    wn
    #
    wph
    @2
    cN
    cF
    cfv
    #
    c1
    cle
    wbr
    #
    wph
    c1
    @4
    clt
    wbr
    #
    @5
    wn
    #
    ostth2.3
    wph
    c1
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @6
    @7
    wb
    1re
    wph
    cF
    cA
    wcel
    #
    cN
    cq
    wcel
    #
    @9
    ostth.1
    wph
    cN
    cn
    wcel
    #
    @11
    wph
    @12
    c1
    cN
    clt
    wbr
    #
    wph
    cN
    c2
    cuz
    cfv
    #
    wcel
    @12
    @13
    wa
    ostth2.2
    cN
    eluz2b2
    sylib
    #
    simpld
    #
    cN
    nnq
    syl
    cA
    cq
    cQ
    cF
    cN
    qabsabv.a
    cQ
    qrng.q
    qrngbas
    #
    abvcl
    syl2anc
    #
    c1
    @4
    ltnle
    sylancr
    mpbid
    wph
    @2
    wa
    @4
    cT
    cU
    ccxp
    co
    #
    c1
    cle
    wph
    @4
    @19
    cle
    wbr
    @2
    wph
    @4
    @19
    c1
    cmul
    co
    #
    @19
    cle
    wph
    @4
    @19
    cdiv
    co
    #
    c1
    cle
    wbr
    @4
    @20
    cle
    wbr
    wph
    @21
    cM
    cT
    cmul
    co
    #
    cU
    c1
    caddc
    co
    #
    cmul
    co
    vn
    wph
    @4
    @19
    @18
    wph
    cT
    cU
    wph
    cT
    wph
    cT
    @2
    c1
    @0
    cif
    #
    cr
    ostth2.7
    wph
    @8
    @0
    cr
    wcel
    #
    @24
    cr
    wcel
    1re
    wph
    @10
    cM
    cq
    wcel
    #
    @25
    ostth.1
    wph
    cM
    cn
    wcel
    #
    @26
    wph
    @27
    c1
    cM
    clt
    wbr
    #
    wph
    cM
    @14
    wcel
    @27
    @28
    wa
    ostth2.5
    cM
    eluz2b2
    sylib
    #
    simpld
    #
    cM
    nnq
    syl
    cA
    cq
    cQ
    cF
    cM
    qabsabv.a
    @17
    abvcl
    syl2anc
    #
    @2
    c1
    @0
    cr
    ifcl
    sylancr
    syl5eqel
    #
    wph
    cc0
    c1
    cT
    wph
    0red
    #
    @8
    wph
    1re
    a1i
    #
    @32
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    #
    wph
    c1
    @24
    cT
    cle
    wph
    @25
    @8
    c1
    @24
    cle
    wbr
    @31
    1re
    @0
    c1
    max2
    sylancl
    ostth2.7
    syl6breqr
    ltletrd
    elrpd
    wph
    cU
    cN
    clog
    cfv
    #
    cM
    clog
    cfv
    #
    cdiv
    co
    #
    cr
    ostth2.8
    wph
    @36
    @37
    wph
    cN
    wph
    cN
    @16
    nnrpd
    relogcld
    #
    wph
    cM
    wph
    cM
    @30
    nnred
    #
    wph
    @27
    @28
    @29
    simprd
    rplogcld
    #
    rerpdivcld
    syl5eqel
    #
    rpcxpcld
    #
    rerpdivcld
    wph
    @22
    @23
    wph
    cM
    cT
    @40
    @32
    remulcld
    wph
    cU
    cr
    wcel
    @23
    cr
    wcel
    @42
    cU
    peano2re
    syl
    remulcld
    wph
    vx
    cA
    cQ
    cR
    cS
    cT
    cU
    cF
    cJ
    cK
    cM
    cN
    vn
    cv
    vq
    qrng.q
    qabsabv.a
    padic.j
    ostth.k
    ostth.1
    ostth2.2
    ostth2.3
    ostth2.4
    ostth2.5
    ostth2.6
    ostth2.7
    ostth2.8
    ostth2lem3
    ostth2lem1
    wph
    @4
    c1
    @19
    @18
    @34
    @43
    ledivmuld
    mpbid
    wph
    @19
    wph
    @19
    @43
    rpcnd
    mulid1d
    breqtrd
    #
    adantr
    @2
    wph
    @19
    c1
    cU
    ccxp
    co
    c1
    @2
    cT
    c1
    cU
    ccxp
    @2
    cT
    @24
    c1
    ostth2.7
    @2
    c1
    @0
    iftrue
    syl5eq
    oveq1d
    wph
    cU
    wph
    cU
    @42
    recnd
    #
    1cxpd
    sylan9eqr
    breqtrd
    mtand
    #
    wph
    @8
    @25
    @1
    @3
    wb
    1re
    @31
    c1
    @0
    ltnle
    sylancr
    mpbird
    #
    wph
    @4
    clog
    cfv
    #
    @36
    cdiv
    co
    #
    @0
    clog
    cfv
    #
    @37
    cdiv
    co
    #
    cR
    cS
    cle
    wph
    @49
    @51
    cle
    wbr
    @48
    @36
    @51
    cmul
    co
    #
    cle
    wbr
    wph
    @48
    cU
    @50
    cmul
    co
    #
    @52
    cle
    wph
    @48
    @53
    cle
    wbr
    #
    @48
    ce
    cfv
    #
    @53
    ce
    cfv
    #
    cle
    wbr
    #
    wph
    @4
    @19
    @55
    @56
    cle
    @44
    wph
    @4
    wph
    @4
    @18
    wph
    cc0
    c1
    @4
    @33
    @34
    @18
    @35
    ostth2.3
    lttrd
    elrpd
    #
    reeflogd
    wph
    @19
    @0
    cU
    ccxp
    co
    @56
    wph
    cT
    @0
    cU
    ccxp
    wph
    @3
    cT
    @0
    wceq
    @46
    @3
    cT
    @24
    @0
    ostth2.7
    @2
    c1
    @0
    iffalse
    syl5eq
    syl
    oveq1d
    wph
    @0
    cU
    wph
    @0
    @31
    recnd
    wph
    @0
    wph
    @0
    @31
    wph
    cc0
    c1
    @0
    @33
    @34
    @31
    @35
    @47
    lttrd
    elrpd
    #
    rpne0d
    @45
    cxpefd
    eqtr2d
    3brtr4d
    wph
    @48
    cr
    wcel
    @53
    cr
    wcel
    @54
    @57
    wb
    wph
    @4
    @58
    relogcld
    #
    wph
    cU
    @50
    @42
    wph
    @0
    @59
    relogcld
    #
    remulcld
    @48
    @53
    efle
    syl2anc
    mpbird
    wph
    @52
    @50
    cU
    cmul
    co
    #
    @53
    wph
    @52
    @50
    @38
    cmul
    co
    @62
    wph
    @36
    @50
    @37
    wph
    @36
    @39
    recnd
    wph
    @50
    @61
    recnd
    #
    wph
    @37
    @41
    rpcnd
    wph
    @37
    @41
    rpne0d
    div12d
    cU
    @38
    @50
    cmul
    ostth2.8
    oveq2i
    syl6eqr
    wph
    @50
    cU
    @63
    @45
    mulcomd
    eqtrd
    breqtrrd
    wph
    @48
    @51
    @36
    @60
    wph
    @50
    @37
    @61
    @41
    rerpdivcld
    wph
    cN
    wph
    cN
    @16
    nnred
    wph
    @12
    @13
    @15
    simprd
    rplogcld
    ledivmuld
    mpbird
    ostth2.4
    ostth2.6
    3brtr4g
    jca
end
