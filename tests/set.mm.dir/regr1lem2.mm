include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "creg.mm"
include "wa.mm"
include "ckq.mm"
include "cha.mm"
include "cv.mm"
include "wne.mm"
include "wel.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "crn.mm"
include "wral.mm"
include "wn.mm"
include "wb.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprl.mm"
include "simprr.mm"
include "regr1lem.mm"
include "3ancoma.mm"
include "incom.mm"
include "eqeq1i.mm"
include "3anbi3i.mm"
include "bitri.mm"
include "2rexbii.mm"
include "rexcom.mm"
include "sylnib.mm"
include "impbid.mm"
include "expr.mm"
include "ralrimdva.mm"
include "kqfeq.mm"
include "elequ2.mm"
include "bibi12d.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "3expb.mm"
include "adantlr.mm"
include "sylibrd.mm"
include "necon1ad.mm"
include "ralrimivva.mm"
include "wfn.mm"
include "kqffn.mm"
include "adantr.mm"
include "neeq1.mm"
include "eleq1.mm"
include "3anbi1d.mm"
include "2rexbidv.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "ralrn.mm"
include "neeq2.mm"
include "3anbi2d.mm"
include "bitrd.mm"
include "syl.mm"
include "mpbird.mm"
include "kqtopon.mm"
include "ishaus2.mm"

theorem regr1lem2
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cJ: class J
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vu: setvar u
  let vv: setvar v
  let wph: wff ph
  let cU: class U
  let cV: class V
  assume kqval.2: |- F = ( x e. X |-> { y e. J | x e. y } )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint m n
  disjoint m o
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n o
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint A o
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B m
  disjoint B n
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a o
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint b j
  disjoint b m
  disjoint b n
  disjoint b o
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint J b
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint m u
  disjoint m v
  disjoint J m
  disjoint n u
  disjoint n v
  disjoint J n
  disjoint o u
  disjoint o v
  disjoint J o
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint J w
  disjoint J z
  disjoint F a
  disjoint F b
  disjoint F m
  disjoint F n
  disjoint F o
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F z
  disjoint ph w
  disjoint ph z
  disjoint X a
  disjoint X b
  disjoint X m
  disjoint X n
  disjoint X o
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint U w
  disjoint U z
  disjoint V x
  assert |- ( ( J e. ( TopOn ` X ) /\ J e. Reg ) -> ( KQ ` J ) e. Haus )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cJ
    creg
    wcel
    #
    wa
    #
    cJ
    ckq
    cfv
    #
    cha
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    va
    vm
    wel
    #
    vb
    vn
    wel
    #
    vm
    cv
    #
    vn
    cv
    #
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vn
    @4
    wrex
    vm
    @4
    wrex
    #
    wi
    #
    vb
    cF
    crn
    #
    wral
    #
    va
    @18
    wral
    #
    @3
    @20
    vz
    cv
    #
    cF
    cfv
    #
    vw
    cv
    #
    cF
    cfv
    #
    wne
    #
    @22
    @11
    wcel
    #
    @24
    @12
    wcel
    #
    @14
    w3a
    #
    vn
    @4
    wrex
    vm
    @4
    wrex
    #
    wi
    #
    vw
    cX
    wral
    #
    vz
    cX
    wral
    #
    @3
    @30
    vz
    vw
    cX
    cX
    @3
    @21
    cX
    wcel
    #
    @23
    cX
    wcel
    #
    wa
    #
    wa
    #
    @29
    @22
    @24
    @36
    @29
    wn
    #
    vz
    va
    wel
    #
    vw
    va
    wel
    #
    wb
    #
    va
    cJ
    wral
    #
    @22
    @24
    wceq
    #
    @36
    @37
    @40
    va
    cJ
    @36
    @6
    cJ
    wcel
    #
    @37
    @40
    @36
    @43
    @37
    wa
    #
    wa
    #
    @38
    @39
    @45
    vx
    vy
    @21
    @23
    @6
    vm
    vn
    cF
    cJ
    cX
    kqval.2
    @1
    @2
    @35
    @44
    simplll
    #
    @1
    @2
    @35
    @44
    simpllr
    #
    @3
    @33
    @34
    @44
    simplrl
    #
    @3
    @33
    @34
    @44
    simplrr
    #
    @36
    @43
    @37
    simprl
    #
    @36
    @43
    @37
    simprr
    #
    regr1lem
    @45
    vx
    vy
    @23
    @21
    @6
    vn
    vm
    cF
    cJ
    cX
    kqval.2
    @46
    @47
    @49
    @48
    @50
    @45
    @29
    @27
    @26
    @12
    @11
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vm
    @4
    wrex
    vn
    @4
    wrex
    #
    @51
    @29
    @54
    vn
    @4
    wrex
    vm
    @4
    wrex
    @55
    @28
    @54
    vm
    vn
    @4
    @4
    @28
    @27
    @26
    @14
    w3a
    @54
    @26
    @27
    @14
    3ancoma
    @14
    @53
    @27
    @26
    @13
    @52
    c0
    @11
    @12
    incom
    eqeq1i
    3anbi3i
    bitri
    2rexbii
    @54
    vm
    vn
    @4
    @4
    rexcom
    bitri
    sylnib
    regr1lem
    impbid
    expr
    ralrimdva
    @1
    @35
    @42
    @41
    wb
    #
    @2
    @1
    @33
    @34
    @56
    @1
    @33
    @34
    w3a
    @42
    vz
    vy
    wel
    #
    vw
    vy
    wel
    #
    wb
    #
    vy
    cJ
    wral
    @41
    vx
    vy
    @21
    @23
    cF
    cJ
    @0
    cX
    kqval.2
    kqfeq
    @59
    @40
    vy
    va
    cJ
    vy
    cv
    @6
    wceq
    @57
    @38
    @58
    @39
    vy
    va
    vz
    elequ2
    vy
    va
    vw
    elequ2
    bibi12d
    cbvralv
    syl6bb
    3expb
    adantlr
    sylibrd
    necon1ad
    ralrimivva
    @3
    cF
    cX
    wfn
    #
    @20
    @32
    wb
    @1
    @60
    @2
    vx
    vy
    cF
    cJ
    @0
    cX
    kqval.2
    kqffn
    adantr
    @60
    @20
    @22
    @7
    wne
    #
    @26
    @10
    @14
    w3a
    #
    vn
    @4
    wrex
    vm
    @4
    wrex
    #
    wi
    #
    vb
    @18
    wral
    #
    vz
    cX
    wral
    @32
    @19
    @65
    va
    vz
    cX
    cF
    @6
    @22
    wceq
    #
    @17
    @64
    vb
    @18
    @66
    @8
    @61
    @16
    @63
    @6
    @22
    @7
    neeq1
    @66
    @15
    @62
    vm
    vn
    @4
    @4
    @66
    @9
    @26
    @10
    @14
    @6
    @22
    @11
    eleq1
    3anbi1d
    2rexbidv
    imbi12d
    ralbidv
    ralrn
    @60
    @65
    @31
    vz
    cX
    @64
    @30
    vb
    vw
    cX
    cF
    @7
    @24
    wceq
    #
    @61
    @25
    @63
    @29
    @7
    @24
    @22
    neeq2
    @67
    @62
    @28
    vm
    vn
    @4
    @4
    @67
    @10
    @27
    @26
    @14
    @7
    @24
    @12
    eleq1
    3anbi2d
    2rexbidv
    imbi12d
    ralrn
    ralbidv
    bitrd
    syl
    mpbird
    @3
    @4
    @18
    ctopon
    cfv
    wcel
    #
    @5
    @20
    wb
    @1
    @68
    @2
    vx
    vy
    cF
    cJ
    cX
    kqval.2
    kqtopon
    adantr
    va
    vb
    vn
    vm
    @4
    @18
    ishaus2
    syl
    mpbird
end
