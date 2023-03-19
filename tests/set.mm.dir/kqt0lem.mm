include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ckq.mm"
include "ct0.mm"
include "wel.mm"
include "wb.mm"
include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "crn.mm"
include "wa.mm"
include "cima.mm"
include "kqopn.mm"
include "adantlr.mm"
include "eleq2.mm"
include "bibi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "kqfvima.mm"
include "3expa.mm"
include "adantrr.mm"
include "adantrl.mm"
include "an32s.mm"
include "sylibrd.mm"
include "ralrimdva.mm"
include "kqfeq.mm"
include "3expb.mm"
include "elequ2.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "ralrimivva.mm"
include "wfn.mm"
include "kqffn.mm"
include "eleq1.mm"
include "bibi1d.mm"
include "ralbidv.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "ralrn.mm"
include "bibi2d.mm"
include "eqeq2.mm"
include "bitrd.mm"
include "mpbird.mm"
include "kqtopon.mm"
include "ist0-2.mm"

theorem kqt0lem
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
  assert |- ( J e. ( TopOn ` X ) -> ( KQ ` J ) e. Kol2 )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cJ
    ckq
    cfv
    #
    ct0
    wcel
    #
    vu
    vz
    wel
    #
    vv
    vz
    wel
    #
    wb
    #
    vz
    @2
    wral
    #
    vu
    cv
    #
    vv
    cv
    #
    wceq
    #
    wi
    #
    vv
    cF
    crn
    #
    wral
    #
    vu
    @12
    wral
    #
    @1
    @14
    va
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    wcel
    #
    vb
    cv
    #
    cF
    cfv
    #
    @17
    wcel
    #
    wb
    #
    vz
    @2
    wral
    #
    @16
    @20
    wceq
    #
    wi
    #
    vb
    cX
    wral
    #
    va
    cX
    wral
    #
    @1
    @25
    va
    vb
    cX
    cX
    @1
    @15
    cX
    wcel
    #
    @19
    cX
    wcel
    #
    wa
    #
    wa
    #
    @23
    va
    vw
    wel
    #
    vb
    vw
    wel
    #
    wb
    #
    vw
    cJ
    wral
    #
    @24
    @31
    @23
    @34
    vw
    cJ
    @31
    vw
    cv
    #
    cJ
    wcel
    #
    wa
    #
    @23
    @16
    cF
    @36
    cima
    #
    wcel
    #
    @20
    @39
    wcel
    #
    wb
    #
    @34
    @38
    @39
    @2
    wcel
    #
    @23
    @42
    wi
    @1
    @37
    @43
    @30
    vx
    vy
    @36
    cF
    cJ
    cX
    kqval.2
    kqopn
    adantlr
    @22
    @42
    vz
    @39
    @2
    @17
    @39
    wceq
    @18
    @40
    @21
    @41
    @17
    @39
    @16
    eleq2
    @17
    @39
    @20
    eleq2
    bibi12d
    rspcv
    syl
    @1
    @37
    @30
    @34
    @42
    wb
    @1
    @37
    wa
    #
    @30
    wa
    @32
    @40
    @33
    @41
    @44
    @28
    @32
    @40
    wb
    #
    @29
    @1
    @37
    @28
    @45
    vx
    vy
    @15
    @36
    cF
    cJ
    cX
    kqval.2
    kqfvima
    3expa
    adantrr
    @44
    @29
    @33
    @41
    wb
    #
    @28
    @1
    @37
    @29
    @46
    vx
    vy
    @19
    @36
    cF
    cJ
    cX
    kqval.2
    kqfvima
    3expa
    adantrl
    bibi12d
    an32s
    sylibrd
    ralrimdva
    @31
    @24
    va
    vy
    wel
    #
    vb
    vy
    wel
    #
    wb
    #
    vy
    cJ
    wral
    #
    @35
    @1
    @28
    @29
    @24
    @50
    wb
    vx
    vy
    @15
    @19
    cF
    cJ
    @0
    cX
    kqval.2
    kqfeq
    3expb
    @49
    @34
    vy
    vw
    cJ
    vy
    cv
    @36
    wceq
    @47
    @32
    @48
    @33
    vy
    vw
    va
    elequ2
    vy
    vw
    vb
    elequ2
    bibi12d
    cbvralv
    syl6bb
    sylibrd
    ralrimivva
    @1
    cF
    cX
    wfn
    #
    @14
    @27
    wb
    vx
    vy
    cF
    cJ
    @0
    cX
    kqval.2
    kqffn
    @51
    @14
    @18
    @5
    wb
    #
    vz
    @2
    wral
    #
    @16
    @9
    wceq
    #
    wi
    #
    vv
    @12
    wral
    #
    va
    cX
    wral
    @27
    @13
    @56
    vu
    va
    cX
    cF
    @8
    @16
    wceq
    #
    @11
    @55
    vv
    @12
    @57
    @7
    @53
    @10
    @54
    @57
    @6
    @52
    vz
    @2
    @57
    @4
    @18
    @5
    @8
    @16
    @17
    eleq1
    bibi1d
    ralbidv
    @8
    @16
    @9
    eqeq1
    imbi12d
    ralbidv
    ralrn
    @51
    @56
    @26
    va
    cX
    @55
    @25
    vv
    vb
    cX
    cF
    @9
    @20
    wceq
    #
    @53
    @23
    @54
    @24
    @58
    @52
    @22
    vz
    @2
    @58
    @5
    @21
    @18
    @9
    @20
    @17
    eleq1
    bibi2d
    ralbidv
    @9
    @20
    @16
    eqeq2
    imbi12d
    ralrn
    ralbidv
    bitrd
    syl
    mpbird
    @1
    @2
    @12
    ctopon
    cfv
    wcel
    @3
    @14
    wb
    vx
    vy
    cF
    cJ
    cX
    kqval.2
    kqtopon
    vu
    vv
    vz
    @2
    @12
    ist0-2
    syl
    mpbird
end
