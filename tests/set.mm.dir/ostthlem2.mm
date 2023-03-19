include "cv.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "wceq.mm"
include "eluz2nn.mm"
include "wi.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "cc0.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "qrng1.mm"
include "qrng0.mm"
include "abv1z.mm"
include "sylancl.mm"
include "eqtr4d.mm"
include "cprime.mm"
include "expcom.mm"
include "wa.mm"
include "jcab.mm"
include "oveq12.mm"
include "cq.mm"
include "adantr.mm"
include "cz.mm"
include "eluzelz.mm"
include "ad2antrl.mm"
include "zq.mm"
include "syl.mm"
include "ad2antll.mm"
include "qrngbas.mm"
include "cvv.mm"
include "cmulr.mm"
include "qex.mm"
include "ccnfld.mm"
include "cnfldmul.mm"
include "ressmulr.mm"
include "ax-mp.mm"
include "abvmul.mm"
include "syl3anc.mm"
include "syl5ibr.mm"
include "a2d.mm"
include "syl5bir.mm"
include "prmind.mm"
include "impcom.mm"
include "sylan2.mm"
include "ostthlem1.mm"

theorem ostthlem2
  let wph: wff ph
  let cA: class A
  let cQ: class Q
  let cF: class F
  let cG: class G
  let vp: setvar p
  let vk: setvar k
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let vj: setvar j
  let vx: setvar x
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  let vg: setvar g
  let cJ: class J
  let cS: class S
  let cT: class T
  let cU: class U
  let cX: class X
  let cN: class N
  let cY: class Y
  let cP: class P
  let cR: class R
  assume qrng.q: |- Q = ( CCfld |`s QQ )
  assume qabsabv.a: |- A = ( AbsVal ` Q )
  assume ostthlem1.1: |- ( ph -> F e. A )
  assume ostthlem1.2: |- ( ph -> G e. A )
  assume ostthlem2.3: |- ( ( ph /\ p e. Prime ) -> ( F ` p ) = ( G ` p ) )

  disjoint G p
  disjoint p ph
  disjoint A p
  disjoint F p
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
  disjoint M x
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
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint ph q
  disjoint x y
  disjoint x z
  disjoint ph x
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
  disjoint T x
  disjoint U n
  disjoint U x
  disjoint X k
  disjoint X x
  disjoint A a
  disjoint A k
  disjoint A n
  disjoint A q
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Q k
  disjoint Q n
  disjoint Q x
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
  disjoint F q
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
  disjoint R q
  disjoint R y
  disjoint R z
  assert |- ( ph -> F = G )

  proof
    wph
    cA
    cQ
    vn
    cF
    cG
    qrng.q
    qabsabv.a
    ostthlem1.1
    ostthlem1.2
    vn
    cv
    #
    c2
    cuz
    cfv
    #
    wcel
    wph
    @0
    cn
    wcel
    #
    @0
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    wceq
    #
    @0
    eluz2nn
    @2
    wph
    @5
    wph
    vp
    cv
    #
    cF
    cfv
    #
    @6
    cG
    cfv
    #
    wceq
    #
    wi
    wph
    c1
    cF
    cfv
    #
    c1
    cG
    cfv
    #
    wceq
    #
    wi
    wph
    vy
    cv
    #
    cF
    cfv
    #
    @13
    cG
    cfv
    #
    wceq
    #
    wi
    #
    wph
    vz
    cv
    #
    cF
    cfv
    #
    @18
    cG
    cfv
    #
    wceq
    #
    wi
    #
    wph
    @13
    @18
    cmul
    co
    #
    cF
    cfv
    #
    @23
    cG
    cfv
    #
    wceq
    #
    wi
    #
    wph
    @5
    wi
    vp
    vy
    vz
    @0
    @6
    c1
    wceq
    #
    @9
    @12
    wph
    @28
    @7
    @10
    @8
    @11
    @6
    c1
    cF
    fveq2
    @6
    c1
    cG
    fveq2
    eqeq12d
    imbi2d
    @6
    @13
    wceq
    #
    @9
    @16
    wph
    @29
    @7
    @14
    @8
    @15
    @6
    @13
    cF
    fveq2
    @6
    @13
    cG
    fveq2
    eqeq12d
    imbi2d
    @6
    @18
    wceq
    #
    @9
    @21
    wph
    @30
    @7
    @19
    @8
    @20
    @6
    @18
    cF
    fveq2
    @6
    @18
    cG
    fveq2
    eqeq12d
    imbi2d
    @6
    @23
    wceq
    #
    @9
    @26
    wph
    @31
    @7
    @24
    @8
    @25
    @6
    @23
    cF
    fveq2
    @6
    @23
    cG
    fveq2
    eqeq12d
    imbi2d
    @6
    @0
    wceq
    #
    @9
    @5
    wph
    @32
    @7
    @3
    @8
    @4
    @6
    @0
    cF
    fveq2
    @6
    @0
    cG
    fveq2
    eqeq12d
    imbi2d
    wph
    @10
    c1
    @11
    wph
    cF
    cA
    wcel
    #
    c1
    cc0
    wne
    #
    @10
    c1
    wceq
    ostthlem1.1
    ax-1ne0
    cA
    cQ
    c1
    cF
    cc0
    qabsabv.a
    cQ
    qrng.q
    qrng1
    #
    cQ
    qrng.q
    qrng0
    #
    abv1z
    sylancl
    wph
    cG
    cA
    wcel
    #
    @34
    @11
    c1
    wceq
    ostthlem1.2
    ax-1ne0
    cA
    cQ
    c1
    cG
    cc0
    qabsabv.a
    @35
    @36
    abv1z
    sylancl
    eqtr4d
    wph
    @6
    cprime
    wcel
    @9
    ostthlem2.3
    expcom
    @17
    @22
    wa
    wph
    @16
    @21
    wa
    #
    wi
    @13
    @1
    wcel
    #
    @18
    @1
    wcel
    #
    wa
    #
    @27
    wph
    @16
    @21
    jcab
    @41
    wph
    @38
    @26
    wph
    @41
    @38
    @26
    wi
    @38
    @26
    wph
    @41
    wa
    #
    @14
    @19
    cmul
    co
    #
    @15
    @20
    cmul
    co
    #
    wceq
    @14
    @15
    @19
    @20
    cmul
    oveq12
    @42
    @24
    @43
    @25
    @44
    @42
    @33
    @13
    cq
    wcel
    #
    @18
    cq
    wcel
    #
    @24
    @43
    wceq
    wph
    @33
    @41
    ostthlem1.1
    adantr
    @42
    @13
    cz
    wcel
    #
    @45
    @39
    @47
    wph
    @40
    c2
    @13
    eluzelz
    ad2antrl
    @13
    zq
    syl
    #
    @42
    @18
    cz
    wcel
    #
    @46
    @40
    @49
    wph
    @39
    c2
    @18
    eluzelz
    ad2antll
    @18
    zq
    syl
    #
    cA
    cq
    cQ
    cmul
    cF
    @13
    @18
    qabsabv.a
    cQ
    qrng.q
    qrngbas
    #
    cq
    cvv
    wcel
    cmul
    cQ
    cmulr
    cfv
    wceq
    qex
    cq
    ccnfld
    cQ
    cmul
    cvv
    qrng.q
    cnfldmul
    ressmulr
    ax-mp
    #
    abvmul
    syl3anc
    @42
    @37
    @45
    @46
    @25
    @44
    wceq
    wph
    @37
    @41
    ostthlem1.2
    adantr
    @48
    @50
    cA
    cq
    cQ
    cmul
    cG
    @13
    @18
    qabsabv.a
    @51
    @52
    abvmul
    syl3anc
    eqeq12d
    syl5ibr
    expcom
    a2d
    syl5bir
    prmind
    impcom
    sylan2
    ostthlem1
end
