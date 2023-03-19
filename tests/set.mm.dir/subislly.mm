include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "clly.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "wss.mm"
include "w3a.mm"
include "wb.mm"
include "resttop.mm"
include "islly.mm"
include "baib.mm"
include "syl.mm"
include "cvv.mm"
include "vex.mm"
include "inex1.mm"
include "a1i.mm"
include "elrest.mm"
include "wceq.mm"
include "simpr.mm"
include "raleqdv.mm"
include "elin.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "rexbii2.mm"
include "ad2antrr.mm"
include "3anass.mm"
include "simpllr.mm"
include "sseq12d.mm"
include "selpw.mm"
include "inss2.mm"
include "biantru.mm"
include "ssin.mm"
include "3bitr4g.mm"
include "eleq2d.mm"
include "simplr.mm"
include "sseldi.mm"
include "biantrud.mm"
include "syl6bbr.mm"
include "bitr4d.mm"
include "oveq2d.mm"
include "simp-4l.mm"
include "restabs.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "3anbi123d.mm"
include "syl5bbr.mm"
include "rexxfr2d.mm"
include "syl5bb.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "ralxfr2d.mm"

theorem subislly
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cJ: class J
  let cV: class V
  let vj: setvar j
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  let cP: class P
  let cU: class U

  disjoint u x
  disjoint u y
  disjoint A u
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B u
  disjoint B x
  disjoint B y
  disjoint J u
  disjoint J x
  disjoint J y
  disjoint V u
  disjoint V x
  disjoint V y
  disjoint j s
  disjoint j u
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u w
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B j
  disjoint B w
  disjoint B z
  disjoint P s
  disjoint P u
  disjoint P y
  disjoint U s
  disjoint U u
  disjoint U x
  disjoint U y
  disjoint J j
  disjoint J s
  disjoint J w
  disjoint J z
  disjoint V w
  disjoint V z
  assert |- ( ( J e. Top /\ B e. V ) -> ( ( J |`t B ) e. Locally A <-> A. x e. J A. y e. ( x i^i B ) E. u e. J ( ( u i^i B ) C_ x /\ y e. u /\ ( J |`t ( u i^i B ) ) e. A ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cJ
    cB
    crest
    co
    #
    cA
    clly
    wcel
    #
    vy
    cv
    #
    vw
    cv
    #
    wcel
    #
    @3
    @6
    crest
    co
    #
    cA
    wcel
    #
    wa
    #
    vw
    @3
    vz
    cv
    #
    cpw
    #
    cin
    #
    wrex
    #
    vy
    @11
    wral
    #
    vz
    @3
    wral
    #
    vu
    cv
    #
    cB
    cin
    #
    vx
    cv
    #
    wss
    #
    @5
    @17
    wcel
    #
    cJ
    @18
    crest
    co
    #
    cA
    wcel
    #
    w3a
    #
    vu
    cJ
    wrex
    #
    vy
    @19
    cB
    cin
    #
    wral
    #
    vx
    cJ
    wral
    @2
    @3
    ctop
    wcel
    #
    @4
    @16
    wb
    cB
    cJ
    cV
    resttop
    @4
    @28
    @16
    vz
    vy
    vw
    cA
    @3
    islly
    baib
    syl
    @2
    @15
    @27
    vz
    vx
    @26
    @3
    cJ
    cvv
    @26
    cvv
    wcel
    @2
    @19
    cJ
    wcel
    wa
    @19
    cB
    vx
    vex
    inex1
    a1i
    vx
    @11
    cB
    cJ
    ctop
    cV
    elrest
    @2
    @11
    @26
    wceq
    #
    wa
    #
    @15
    @14
    vy
    @26
    wral
    @27
    @30
    @14
    vy
    @11
    @26
    @2
    @29
    simpr
    raleqdv
    @30
    @14
    @25
    vy
    @26
    @14
    @6
    @12
    wcel
    #
    @10
    wa
    #
    vw
    @3
    wrex
    @30
    @5
    @26
    wcel
    #
    wa
    #
    @25
    @10
    @32
    vw
    @13
    @3
    @6
    @13
    wcel
    #
    @10
    wa
    @6
    @3
    wcel
    #
    @31
    wa
    #
    @10
    wa
    @36
    @32
    wa
    @35
    @37
    @10
    @6
    @3
    @12
    elin
    anbi1i
    @36
    @31
    @10
    anass
    bitri
    rexbii2
    @34
    @32
    @24
    vw
    vu
    @18
    @3
    cJ
    cvv
    @18
    cvv
    wcel
    @34
    @17
    cJ
    wcel
    wa
    @17
    cB
    vu
    vex
    inex1
    a1i
    @2
    @36
    @6
    @18
    wceq
    #
    vu
    cJ
    wrex
    wb
    @29
    @33
    vu
    @6
    cB
    cJ
    ctop
    cV
    elrest
    ad2antrr
    @32
    @31
    @7
    @9
    w3a
    @34
    @38
    wa
    #
    @24
    @31
    @7
    @9
    3anass
    @39
    @31
    @20
    @7
    @21
    @9
    @23
    @39
    @6
    @11
    wss
    @18
    @26
    wss
    #
    @31
    @20
    @39
    @6
    @18
    @11
    @26
    @34
    @38
    simpr
    #
    @2
    @29
    @33
    @38
    simpllr
    sseq12d
    vw
    @11
    selpw
    @20
    @20
    @18
    cB
    wss
    #
    wa
    @40
    @42
    @20
    @17
    cB
    inss2
    #
    biantru
    @18
    @19
    cB
    ssin
    bitri
    3bitr4g
    @39
    @7
    @5
    @18
    wcel
    #
    @21
    @39
    @6
    @18
    @5
    @41
    eleq2d
    @39
    @21
    @21
    @5
    cB
    wcel
    #
    wa
    @44
    @39
    @45
    @21
    @39
    @26
    cB
    @5
    @19
    cB
    inss2
    @30
    @33
    @38
    simplr
    sseldi
    biantrud
    @5
    @17
    cB
    elin
    syl6bbr
    bitr4d
    @39
    @8
    @22
    cA
    @39
    @8
    @3
    @18
    crest
    co
    #
    @22
    @39
    @6
    @18
    @3
    crest
    @41
    oveq2d
    @39
    @0
    @42
    @1
    @46
    @22
    wceq
    @0
    @1
    @29
    @33
    @38
    simp-4l
    @42
    @39
    @43
    a1i
    @30
    @1
    @33
    @38
    @0
    @1
    @29
    simplr
    ad2antrr
    @18
    cB
    cJ
    ctop
    cV
    restabs
    syl3anc
    eqtrd
    eleq1d
    3anbi123d
    syl5bbr
    rexxfr2d
    syl5bb
    ralbidva
    bitrd
    ralxfr2d
    bitrd
end
