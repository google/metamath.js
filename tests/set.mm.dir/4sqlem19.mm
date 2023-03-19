include "cn0.mm"
include "cv.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "elnn0.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "eleq1.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "abs1.mm"
include "oveq1i.mm"
include "sq1.mm"
include "eqtri.mm"
include "abs0.mm"
include "sq0.mm"
include "oveq12i.mm"
include "1p0e1.mm"
include "cgz.mm"
include "cz.mm"
include "1z.mm"
include "zgz.mm"
include "ax-mp.mm"
include "0z.mm"
include "4sqlem4a.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "cprime.mm"
include "cmin.mm"
include "cfz.mm"
include "wral.mm"
include "wa.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cdiv.mm"
include "oddprm.mm"
include "adantr.mm"
include "cc.mm"
include "eldifi.mm"
include "prmnn.mm"
include "nncn.mm"
include "3syl.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancl.mm"
include "2cnd.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan2d.mm"
include "oveq1d.mm"
include "npcan.mm"
include "eqtr2d.mm"
include "cun.mm"
include "oveq2d.mm"
include "cuz.mm"
include "nnm1nn0.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "eluzfz1.mm"
include "fzsplit.mm"
include "eqtrd.mm"
include "wss.mm"
include "fzsn.mm"
include "00id.mm"
include "snssi.mm"
include "eqsstri.mm"
include "0p1e1.mm"
include "simpr.mm"
include "dfss3.mm"
include "sylibr.mm"
include "syl5eqss.mm"
include "unssd.mm"
include "eqsstrd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "cbvrabv.mm"
include "eqid.mm"
include "4sqlem18.mm"
include "sylanbr.mm"
include "an32s.mm"
include "df-2.mm"
include "eqtr4i.mm"
include "pm2.61ne.mm"
include "wi.mm"
include "mul4sq.mm"
include "prmind2.mm"
include "id.mm"
include "syl6eqel.mm"
include "jaoi.mm"
include "sylbi.mm"
include "ssriv.mm"
include "4sqlem1.mm"
include "eqssi.mm"

theorem 4sqlem19
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cS: class S
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cB: class B
  let cE: class E
  let cG: class G
  let cH: class H
  let vj: setvar j
  let vk: setvar k
  let vv: setvar v
  let cA: class A
  let cC: class C
  let cD: class D
  let cF: class F
  let vi: setvar i
  let vu: setvar u
  let cM: class M
  let vm: setvar m
  let cN: class N
  let cP: class P
  let wph: wff ph
  let cT: class T
  let cR: class R
  assume 4sq.1: |- S = { n | E. x e. ZZ E. y e. ZZ E. z e. ZZ E. w e. ZZ n = ( ( ( x ^ 2 ) + ( y ^ 2 ) ) + ( ( z ^ 2 ) + ( w ^ 2 ) ) ) }

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
  disjoint S n
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
  disjoint B n
  disjoint E n
  disjoint G n
  disjoint H n
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
  disjoint A n
  disjoint A v
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C n
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D n
  disjoint F j
  disjoint F n
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
  disjoint i n
  disjoint i u
  disjoint M i
  disjoint k u
  disjoint M k
  disjoint n u
  disjoint M n
  disjoint M u
  disjoint k m
  disjoint N k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint N m
  disjoint N n
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
  disjoint P i
  disjoint j m
  disjoint j u
  disjoint P j
  disjoint P k
  disjoint P m
  disjoint P n
  disjoint P u
  disjoint P v
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S u
  disjoint S v
  disjoint T k
  disjoint T u
  disjoint R i
  assert |- NN0 = S

  proof
    cn0
    cS
    vk
    cn0
    cS
    vk
    cv
    #
    cn0
    wcel
    @0
    cn
    wcel
    #
    @0
    cc0
    wceq
    #
    wo
    @0
    cS
    wcel
    #
    @0
    elnn0
    @1
    @3
    @2
    vj
    cv
    #
    cS
    wcel
    #
    c1
    cS
    wcel
    vm
    cv
    #
    cS
    wcel
    #
    vi
    cv
    #
    cS
    wcel
    #
    @6
    @8
    cmul
    co
    #
    cS
    wcel
    #
    @3
    vj
    vm
    vi
    @0
    @4
    c1
    cS
    eleq1
    @4
    @6
    cS
    eleq1
    @4
    @8
    cS
    eleq1
    @4
    @10
    cS
    eleq1
    @4
    @0
    cS
    eleq1
    c1
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cc0
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    c1
    cS
    @16
    c1
    cc0
    caddc
    co
    c1
    @13
    c1
    @15
    cc0
    caddc
    @13
    c1
    c2
    cexp
    co
    c1
    @12
    c1
    c2
    cexp
    abs1
    oveq1i
    sq1
    eqtri
    #
    @15
    cc0
    c2
    cexp
    co
    cc0
    @14
    cc0
    c2
    cexp
    abs0
    oveq1i
    sq0
    eqtri
    #
    oveq12i
    1p0e1
    eqtri
    c1
    cgz
    wcel
    #
    cc0
    cgz
    wcel
    #
    @16
    cS
    wcel
    c1
    cz
    wcel
    @19
    1z
    c1
    zgz
    ax-mp
    #
    cc0
    cz
    wcel
    #
    @20
    0z
    cc0
    zgz
    ax-mp
    #
    vx
    vy
    vz
    vw
    c1
    cc0
    cS
    vn
    4sq.1
    4sqlem4a
    mp2an
    eqeltrri
    @4
    cprime
    wcel
    #
    @7
    vm
    c1
    @4
    c1
    cmin
    co
    #
    cfz
    co
    #
    wral
    #
    wa
    #
    @5
    c2
    cS
    wcel
    #
    @4
    c2
    @4
    c2
    cS
    eleq1
    @24
    @4
    c2
    wne
    #
    @27
    @5
    @24
    @30
    wa
    @4
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    @27
    @5
    @4
    cprime
    c2
    eldifsn
    @32
    @27
    wa
    #
    vx
    vy
    vz
    vw
    @4
    cS
    @0
    @4
    cmul
    co
    #
    cS
    wcel
    #
    vk
    cn
    crab
    #
    vi
    vn
    @36
    cr
    clt
    cinf
    #
    @25
    c2
    cdiv
    co
    #
    4sq.1
    @32
    @38
    cn
    wcel
    @27
    @4
    oddprm
    adantr
    @33
    c2
    @38
    cmul
    co
    #
    c1
    caddc
    co
    @25
    c1
    caddc
    co
    #
    @4
    @33
    @39
    @25
    c1
    caddc
    @33
    @25
    c2
    @33
    @4
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @25
    cc
    wcel
    @33
    @24
    @4
    cn
    wcel
    #
    @41
    @32
    @24
    @27
    @4
    cprime
    @31
    eldifi
    adantr
    #
    @4
    prmnn
    #
    @4
    nncn
    3syl
    #
    ax-1cn
    @4
    c1
    subcl
    sylancl
    @33
    2cnd
    c2
    cc0
    wne
    @33
    2ne0
    a1i
    divcan2d
    #
    oveq1d
    @33
    @41
    @42
    @40
    @4
    wceq
    @46
    ax-1cn
    @4
    c1
    npcan
    sylancl
    eqtr2d
    @44
    @33
    cc0
    @39
    cfz
    co
    #
    cc0
    cc0
    cfz
    co
    #
    cc0
    c1
    caddc
    co
    #
    @25
    cfz
    co
    #
    cun
    #
    cS
    @33
    @48
    cc0
    @25
    cfz
    co
    #
    @52
    @33
    @39
    @25
    cc0
    cfz
    @47
    oveq2d
    @33
    @25
    cc0
    cuz
    cfv
    wcel
    #
    cc0
    @53
    wcel
    @53
    @52
    wceq
    @33
    @25
    cn0
    wcel
    #
    @54
    @33
    @24
    @43
    @55
    @44
    @45
    @4
    nnm1nn0
    3syl
    @25
    elnn0uz
    sylib
    cc0
    @25
    eluzfz1
    cc0
    cc0
    @25
    fzsplit
    3syl
    eqtrd
    @33
    @49
    @51
    cS
    @49
    cS
    wss
    @33
    @49
    cc0
    csn
    #
    cS
    @22
    @49
    @56
    wceq
    0z
    cc0
    fzsn
    ax-mp
    cc0
    cS
    wcel
    @56
    cS
    wss
    @15
    @15
    caddc
    co
    #
    cc0
    cS
    @57
    cc0
    cc0
    caddc
    co
    cc0
    @15
    cc0
    @15
    cc0
    caddc
    @18
    @18
    oveq12i
    00id
    eqtri
    @20
    @20
    @57
    cS
    wcel
    @23
    @23
    vx
    vy
    vz
    vw
    cc0
    cc0
    cS
    vn
    4sq.1
    4sqlem4a
    mp2an
    eqeltrri
    #
    cc0
    cS
    snssi
    ax-mp
    eqsstri
    a1i
    @33
    @51
    @26
    cS
    @50
    c1
    @25
    cfz
    0p1e1
    oveq1i
    @33
    @27
    @26
    cS
    wss
    @32
    @27
    simpr
    vm
    @26
    cS
    dfss3
    sylibr
    syl5eqss
    unssd
    eqsstrd
    @35
    @8
    @4
    cmul
    co
    #
    cS
    wcel
    vk
    vi
    cn
    @0
    @8
    wceq
    @34
    @59
    cS
    @0
    @8
    @4
    cmul
    oveq1
    eleq1d
    cbvrabv
    @37
    eqid
    4sqlem18
    sylanbr
    an32s
    @29
    @28
    @13
    @13
    caddc
    co
    #
    c2
    cS
    @60
    c1
    c1
    caddc
    co
    c2
    @13
    c1
    @13
    c1
    caddc
    @17
    @17
    oveq12i
    df-2
    eqtr4i
    @19
    @19
    @60
    cS
    wcel
    @21
    @21
    vx
    vy
    vz
    vw
    c1
    c1
    cS
    vn
    4sq.1
    4sqlem4a
    mp2an
    eqeltrri
    a1i
    pm2.61ne
    @7
    @9
    wa
    @11
    wi
    @6
    c2
    cuz
    cfv
    #
    wcel
    @8
    @61
    wcel
    wa
    vx
    vy
    vz
    vw
    @6
    @8
    cS
    vn
    4sq.1
    mul4sq
    a1i
    prmind2
    @2
    @0
    cc0
    cS
    @2
    id
    @58
    syl6eqel
    jaoi
    sylbi
    ssriv
    vx
    vy
    vz
    vw
    cS
    vn
    4sq.1
    4sqlem1
    eqssi
end
