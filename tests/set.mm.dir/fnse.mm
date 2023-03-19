include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "wse.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "crab.mm"
include "cun.mm"
include "ffvelrnda.mm"
include "seex.mm"
include "sylan.mm"
include "syldan.mm"
include "snex.mm"
include "unexg.mm"
include "sylancl.mm"
include "wi.mm"
include "wceq.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "vtoclg.mm"
include "impcom.mm"
include "wss.mm"
include "inss2.mm"
include "wb.mm"
include "vex.mm"
include "eliniseg.mm"
include "ax-mp.mm"
include "wo.mm"
include "fveq2.mm"
include "breqan12d.mm"
include "eqeqan12d.mm"
include "breq12.mm"
include "anbi12d.mm"
include "orbi12d.mm"
include "brab2a.mm"
include "adantrr.mm"
include "breq1.mm"
include "elrab3.mm"
include "syl.mm"
include "biimprd.mm"
include "simpl.mm"
include "fvex.mm"
include "elsn.mm"
include "sylibr.mm"
include "a1i.mm"
include "orim12d.mm"
include "elun.mm"
include "syl6ibr.mm"
include "simprl.mm"
include "jctild.mm"
include "wfn.mm"
include "wf.mm"
include "ffn.mm"
include "adantr.mm"
include "elpreima.mm"
include "sylibrd.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "syl5ss.mm"
include "ssexd.mm"
include "ralrimiva.mm"
include "dfse2.mm"

theorem fnse
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let vz: setvar z
  let vu: setvar u
  assume fnse.1: |- T = { <. x , y >. | ( ( x e. A /\ y e. A ) /\ ( ( F ` x ) R ( F ` y ) \/ ( ( F ` x ) = ( F ` y ) /\ x S y ) ) ) }
  assume fnse.2: |- ( ph -> F : A --> B )
  assume fnse.3: |- ( ph -> R Se B )
  assume fnse.4: |- ( ph -> ( `' F " w ) e. _V )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B w
  disjoint w x
  disjoint w y
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint ph w
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint T w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint u w
  disjoint B u
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint w z
  disjoint ph z
  disjoint R u
  disjoint u z
  disjoint T z
  assert |- ( ph -> T Se A )

  proof
    wph
    cA
    cT
    ccnv
    vz
    cv
    #
    csn
    cima
    #
    cin
    #
    cvv
    wcel
    #
    vz
    cA
    wral
    cA
    cT
    wse
    wph
    @3
    vz
    cA
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @2
    cF
    ccnv
    #
    vu
    cv
    #
    @0
    cF
    cfv
    #
    cR
    wbr
    #
    vu
    cB
    crab
    #
    @8
    csn
    #
    cun
    #
    cima
    #
    cvv
    wph
    @4
    @12
    cvv
    wcel
    #
    @13
    cvv
    wcel
    #
    @5
    @10
    cvv
    wcel
    #
    @11
    cvv
    wcel
    @14
    wph
    @4
    @8
    cB
    wcel
    #
    @16
    wph
    cA
    cB
    @0
    cF
    fnse.2
    ffvelrnda
    wph
    cB
    cR
    wse
    @17
    @16
    fnse.3
    vu
    cB
    @8
    cR
    seex
    sylan
    syldan
    @8
    snex
    @10
    @11
    cvv
    cvv
    unexg
    sylancl
    @14
    wph
    @15
    wph
    @6
    vw
    cv
    #
    cima
    #
    cvv
    wcel
    #
    wi
    wph
    @15
    wi
    vw
    @12
    cvv
    @18
    @12
    wceq
    #
    @20
    @15
    wph
    @21
    @19
    @13
    cvv
    @18
    @12
    @6
    imaeq2
    eleq1d
    imbi2d
    fnse.4
    vtoclg
    impcom
    syldan
    wph
    @2
    @13
    wss
    @4
    wph
    @2
    @1
    @13
    cA
    @1
    inss2
    wph
    vw
    @1
    @13
    @18
    @1
    wcel
    #
    @18
    @0
    cT
    wbr
    #
    wph
    @18
    @13
    wcel
    #
    @0
    cvv
    wcel
    @22
    @23
    wb
    vz
    vex
    cT
    @0
    @18
    cvv
    vw
    vex
    eliniseg
    ax-mp
    @23
    @18
    cA
    wcel
    #
    @4
    wa
    #
    @18
    cF
    cfv
    #
    @8
    cR
    wbr
    #
    @27
    @8
    wceq
    #
    @18
    @0
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    wph
    @24
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cR
    wbr
    #
    @34
    @36
    wceq
    #
    @33
    @35
    cS
    wbr
    #
    wa
    #
    wo
    @32
    vx
    vy
    @18
    @0
    cA
    cA
    cT
    @33
    @18
    wceq
    #
    @35
    @0
    wceq
    #
    wa
    #
    @37
    @28
    @40
    @31
    @41
    @42
    @34
    @27
    @36
    @8
    cR
    @33
    @18
    cF
    fveq2
    #
    @35
    @0
    cF
    fveq2
    #
    breqan12d
    @43
    @38
    @29
    @39
    @30
    @41
    @42
    @34
    @27
    @36
    @8
    @44
    @45
    eqeqan12d
    @33
    @18
    @35
    @0
    cS
    breq12
    anbi12d
    orbi12d
    fnse.1
    brab2a
    wph
    @26
    @32
    @24
    wph
    @26
    wa
    #
    @32
    @25
    @27
    @12
    wcel
    #
    wa
    #
    @24
    @46
    @32
    @47
    @25
    @46
    @32
    @27
    @10
    wcel
    #
    @27
    @11
    wcel
    #
    wo
    @47
    @46
    @28
    @49
    @31
    @50
    @46
    @49
    @28
    @46
    @27
    cB
    wcel
    #
    @49
    @28
    wb
    wph
    @25
    @51
    @4
    wph
    cA
    cB
    @18
    cF
    fnse.2
    ffvelrnda
    adantrr
    @9
    @28
    vu
    @27
    cB
    @7
    @27
    @8
    cR
    breq1
    elrab3
    syl
    biimprd
    @31
    @50
    wi
    @46
    @31
    @29
    @50
    @29
    @30
    simpl
    @27
    @8
    @18
    cF
    fvex
    elsn
    sylibr
    a1i
    orim12d
    @27
    @10
    @11
    elun
    syl6ibr
    wph
    @25
    @4
    simprl
    jctild
    @46
    cF
    cA
    wfn
    #
    @24
    @48
    wb
    wph
    @52
    @26
    wph
    cA
    cB
    cF
    wf
    @52
    fnse.2
    cA
    cB
    cF
    ffn
    syl
    adantr
    cA
    @18
    @12
    cF
    elpreima
    syl
    sylibrd
    expimpd
    syl5bi
    syl5bi
    ssrdv
    syl5ss
    adantr
    ssexd
    ralrimiva
    vz
    cA
    cT
    dfse2
    sylibr
end
