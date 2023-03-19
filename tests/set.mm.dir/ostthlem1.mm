include "cq.mm"
include "wcel.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "qrngbas.mm"
include "abvf.mm"
include "ffn.mm"
include "3syl.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cdiv.mm"
include "co.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "elq.mm"
include "wa.mm"
include "cdvr.mm"
include "cdr.mm"
include "cc0.mm"
include "wne.mm"
include "qdrng.mm"
include "a1i.mm"
include "adantr.mm"
include "zq.mm"
include "ad2antrl.mm"
include "nnq.mm"
include "ad2antll.mm"
include "nnne0.mm"
include "qrng0.mm"
include "eqid.mm"
include "abvdiv.mm"
include "syl23anc.mm"
include "cneg.mm"
include "wi.mm"
include "abv0.mm"
include "syl.mm"
include "eqtr4d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "wral.mm"
include "c1.mm"
include "c2.mm"
include "cuz.mm"
include "wo.mm"
include "elnn1uz2.mm"
include "qrng1.mm"
include "abv1.mm"
include "sylancr.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "rspccva.mm"
include "sylan.mm"
include "cminusg.mm"
include "ad2antrr.mm"
include "adantl.mm"
include "qrngneg.mm"
include "eleq1d.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "ad2antlr.mm"
include "abvneg.mm"
include "3eqtr3d.mm"
include "w3o.mm"
include "elz.mm"
include "simprbi.mm"
include "mpjao3dan.mm"
include "adantrr.mm"
include "adantrl.mm"
include "oveq12d.mm"
include "qrngdiv.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "eqfnfvd.mm"

theorem ostthlem1
  let wph: wff ph
  let cA: class A
  let cQ: class Q
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vp: setvar p
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
  assume ostthlem1.3: |- ( ( ph /\ n e. ( ZZ>= ` 2 ) ) -> ( F ` n ) = ( G ` n ) )

  disjoint G n
  disjoint n ph
  disjoint A n
  disjoint Q n
  disjoint F n
  disjoint k n
  disjoint k p
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint n p
  disjoint n y
  disjoint n z
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
  disjoint p q
  disjoint p x
  disjoint p ph
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
  disjoint A p
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
  disjoint F p
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
    vy
    cq
    cF
    cG
    wph
    cF
    cA
    wcel
    #
    cq
    cr
    cF
    wf
    cF
    cq
    wfn
    ostthlem1.1
    cA
    cq
    cQ
    cF
    qabsabv.a
    cQ
    qrng.q
    qrngbas
    #
    abvf
    cq
    cr
    cF
    ffn
    3syl
    wph
    cG
    cA
    wcel
    #
    cq
    cr
    cG
    wf
    cG
    cq
    wfn
    ostthlem1.2
    cA
    cq
    cQ
    cG
    qabsabv.a
    @1
    abvf
    cq
    cr
    cG
    ffn
    3syl
    wph
    vy
    cv
    #
    cq
    wcel
    #
    @3
    cF
    cfv
    #
    @3
    cG
    cfv
    #
    wceq
    #
    @4
    @3
    vk
    cv
    #
    vn
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vn
    cn
    wrex
    vk
    cz
    wrex
    wph
    @7
    vk
    vn
    @3
    elq
    wph
    @11
    @7
    vk
    vn
    cz
    cn
    wph
    @8
    cz
    wcel
    #
    @9
    cn
    wcel
    #
    wa
    #
    wa
    #
    @7
    @11
    @10
    cF
    cfv
    #
    @10
    cG
    cfv
    #
    wceq
    @15
    @8
    @9
    cQ
    cdvr
    cfv
    #
    co
    #
    cF
    cfv
    #
    @19
    cG
    cfv
    #
    @16
    @17
    @15
    @20
    @8
    cF
    cfv
    #
    @9
    cF
    cfv
    #
    cdiv
    co
    #
    @21
    @15
    cQ
    cdr
    wcel
    #
    @0
    @8
    cq
    wcel
    #
    @9
    cq
    wcel
    #
    @9
    cc0
    wne
    #
    @20
    @24
    wceq
    @25
    @15
    cQ
    qrng.q
    qdrng
    #
    a1i
    #
    wph
    @0
    @14
    ostthlem1.1
    adantr
    @12
    @26
    wph
    @13
    @8
    zq
    #
    ad2antrl
    #
    @13
    @27
    wph
    @12
    @9
    nnq
    ad2antll
    #
    @13
    @28
    wph
    @12
    @9
    nnne0
    ad2antll
    #
    cA
    cq
    @18
    cQ
    cF
    @8
    @9
    cc0
    qabsabv.a
    @1
    cQ
    qrng.q
    qrng0
    #
    @18
    eqid
    #
    abvdiv
    syl23anc
    @15
    @21
    @8
    cG
    cfv
    #
    @9
    cG
    cfv
    #
    cdiv
    co
    #
    @24
    @15
    @25
    @2
    @26
    @27
    @28
    @21
    @39
    wceq
    @30
    wph
    @2
    @14
    ostthlem1.2
    adantr
    @32
    @33
    @34
    cA
    cq
    @18
    cQ
    cG
    @8
    @9
    cc0
    qabsabv.a
    @1
    @35
    @36
    abvdiv
    syl23anc
    @15
    @22
    @37
    @23
    @38
    cdiv
    wph
    @12
    @22
    @37
    wceq
    #
    @13
    wph
    @12
    wa
    #
    @8
    cc0
    wceq
    #
    @40
    @8
    cn
    wcel
    #
    @8
    cneg
    #
    cn
    wcel
    #
    @41
    @42
    @40
    wph
    @42
    @40
    wi
    @12
    wph
    @40
    @42
    cc0
    cF
    cfv
    #
    cc0
    cG
    cfv
    #
    wceq
    wph
    @46
    cc0
    @47
    wph
    @0
    @46
    cc0
    wceq
    ostthlem1.1
    cA
    cQ
    cF
    cc0
    qabsabv.a
    @35
    abv0
    syl
    wph
    @2
    @47
    cc0
    wceq
    ostthlem1.2
    cA
    cQ
    cG
    cc0
    qabsabv.a
    @35
    abv0
    syl
    eqtr4d
    @42
    @22
    @46
    @37
    @47
    @8
    cc0
    cF
    fveq2
    @8
    cc0
    cG
    fveq2
    eqeq12d
    syl5ibrcom
    adantr
    imp
    @41
    @23
    @38
    wceq
    #
    vn
    cn
    wral
    #
    @43
    @40
    wph
    @49
    @12
    wph
    @48
    vn
    cn
    @13
    wph
    @9
    c1
    wceq
    #
    @9
    c2
    cuz
    cfv
    wcel
    #
    wo
    @48
    @9
    elnn1uz2
    wph
    @50
    @48
    @51
    wph
    @50
    @48
    wph
    @48
    @50
    c1
    cF
    cfv
    #
    c1
    cG
    cfv
    #
    wceq
    wph
    @52
    c1
    @53
    wph
    @25
    @0
    @52
    c1
    wceq
    @29
    ostthlem1.1
    cA
    cQ
    c1
    cF
    qabsabv.a
    cQ
    qrng.q
    qrng1
    #
    abv1
    sylancr
    wph
    @25
    @2
    @53
    c1
    wceq
    @29
    ostthlem1.2
    cA
    cQ
    c1
    cG
    qabsabv.a
    @54
    abv1
    sylancr
    eqtr4d
    @50
    @23
    @52
    @38
    @53
    @9
    c1
    cF
    fveq2
    @9
    c1
    cG
    fveq2
    eqeq12d
    syl5ibrcom
    imp
    ostthlem1.3
    jaodan
    sylan2b
    #
    ralrimiva
    #
    adantr
    @48
    @40
    vn
    @8
    cn
    @9
    @8
    wceq
    @23
    @22
    @38
    @37
    @9
    @8
    cF
    fveq2
    @9
    @8
    cG
    fveq2
    eqeq12d
    rspccva
    sylan
    @41
    @45
    wa
    #
    @8
    cQ
    cminusg
    cfv
    #
    cfv
    #
    cF
    cfv
    #
    @59
    cG
    cfv
    #
    @22
    @37
    @57
    @49
    @59
    cn
    wcel
    #
    @60
    @61
    wceq
    #
    wph
    @49
    @12
    @45
    @56
    ad2antrr
    @41
    @62
    @45
    @41
    @59
    @44
    cn
    @41
    @26
    @59
    @44
    wceq
    @12
    @26
    wph
    @31
    adantl
    cQ
    @8
    qrng.q
    qrngneg
    syl
    eleq1d
    biimpar
    @48
    @63
    vn
    @59
    cn
    @9
    @59
    wceq
    @23
    @60
    @38
    @61
    @9
    @59
    cF
    fveq2
    @9
    @59
    cG
    fveq2
    eqeq12d
    rspccva
    syl2anc
    @57
    @0
    @26
    @60
    @22
    wceq
    wph
    @0
    @12
    @45
    ostthlem1.1
    ad2antrr
    @12
    @26
    wph
    @45
    @31
    ad2antlr
    #
    cA
    cq
    cQ
    cF
    @58
    @8
    qabsabv.a
    @1
    @58
    eqid
    #
    abvneg
    syl2anc
    @57
    @2
    @26
    @61
    @37
    wceq
    wph
    @2
    @12
    @45
    ostthlem1.2
    ad2antrr
    @64
    cA
    cq
    cQ
    cG
    @58
    @8
    qabsabv.a
    @1
    @65
    abvneg
    syl2anc
    3eqtr3d
    @12
    @42
    @43
    @45
    w3o
    #
    wph
    @12
    @8
    cr
    wcel
    @66
    @8
    elz
    simprbi
    adantl
    mpjao3dan
    adantrr
    wph
    @13
    @48
    @12
    @55
    adantrl
    oveq12d
    eqtr4d
    eqtr4d
    @15
    @19
    @10
    cF
    @15
    @26
    @27
    @28
    @19
    @10
    wceq
    @32
    @33
    @34
    cQ
    @8
    @9
    qrng.q
    qrngdiv
    syl3anc
    #
    fveq2d
    @15
    @19
    @10
    cG
    @67
    fveq2d
    3eqtr3d
    @11
    @5
    @16
    @6
    @17
    @3
    @10
    cF
    fveq2
    @3
    @10
    cG
    fveq2
    eqeq12d
    syl5ibrcom
    rexlimdvva
    syl5bi
    imp
    eqfnfvd
end
