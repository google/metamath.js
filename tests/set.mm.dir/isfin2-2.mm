include "wcel.mm"
include "cfin2.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "crpss.mm"
include "wor.mm"
include "wa.mm"
include "cint.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wss.mm"
include "elpwi.mm"
include "fin2i2.mm"
include "ex.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "cuni.mm"
include "w3a.mm"
include "wpss.mm"
include "wn.mm"
include "wrex.mm"
include "cdif.mm"
include "crab.mm"
include "simp1r.mm"
include "ssrab2.mm"
include "cvv.mm"
include "wb.mm"
include "simp1l.mm"
include "pwexg.mm"
include "elpw2g.mm"
include "3syl.mm"
include "mpbiri.mm"
include "simp2.mm"
include "simp3l.mm"
include "fin23lem7.mm"
include "syl3anc.mm"
include "sorpsscmpl.mm"
include "adantl.mm"
include "3ad2ant3.mm"
include "jca.mm"
include "wceq.mm"
include "neeq1.mm"
include "soeq2.mm"
include "anbi12d.mm"
include "inteq.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "sorpssint.mm"
include "syl.mm"
include "mpbird.mm"
include "psseq1.mm"
include "pssdifcom1.mm"
include "fin23lem11.mm"
include "sylc.mm"
include "simp3r.mm"
include "sorpssuni.mm"
include "mpbid.mm"
include "3exp.mm"
include "ralrimdva.mm"
include "isfin2.mm"
include "sylibrd.mm"
include "impbid2.mm"

theorem isfin2-2
  let vy: setvar y
  let cA: class A
  let cV: class V
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let cB: class B

  disjoint A y
  disjoint b c
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint c f
  disjoint c m
  disjoint c n
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint A c
  disjoint f m
  disjoint f n
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A z
  disjoint B c
  disjoint B f
  disjoint B m
  disjoint B n
  disjoint B w
  disjoint B x
  disjoint B z
  disjoint V b
  assert |- ( A e. V -> ( A e. Fin2 <-> A. y e. ~P ~P A ( ( y =/= (/) /\ [C.] Or y ) -> |^| y e. y ) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cfin2
    wcel
    #
    vy
    cv
    #
    c0
    wne
    #
    @2
    crpss
    wor
    #
    wa
    #
    @2
    cint
    #
    @2
    wcel
    #
    wi
    #
    vy
    cA
    cpw
    #
    cpw
    #
    wral
    #
    @1
    @8
    vy
    @10
    @2
    @10
    wcel
    @1
    @2
    @9
    wss
    #
    @8
    @2
    @9
    elpwi
    @1
    @12
    wa
    @5
    @7
    cA
    @2
    fin2i2
    ex
    sylan2
    ralrimiva
    @0
    @11
    vb
    cv
    #
    c0
    wne
    #
    @13
    crpss
    wor
    #
    wa
    #
    @13
    cuni
    @13
    wcel
    #
    wi
    #
    vb
    @10
    wral
    @1
    @0
    @11
    @18
    vb
    @10
    @13
    @10
    wcel
    @0
    @13
    @9
    wss
    #
    @11
    @18
    wi
    @13
    @9
    elpwi
    @0
    @19
    wa
    #
    @11
    @16
    @17
    @20
    @11
    @16
    w3a
    #
    vm
    cv
    #
    vn
    cv
    #
    wpss
    #
    wn
    vn
    @13
    wral
    vm
    @13
    wrex
    #
    @17
    @21
    @19
    vw
    cv
    #
    vz
    cv
    #
    wpss
    #
    wn
    vw
    cA
    vc
    cv
    cdif
    @13
    wcel
    #
    vc
    @9
    crab
    #
    wral
    vz
    @30
    wrex
    #
    @25
    @0
    @19
    @11
    @16
    simp1r
    #
    @21
    @31
    @30
    cint
    #
    @30
    wcel
    #
    @21
    @30
    @10
    wcel
    #
    @11
    @30
    c0
    wne
    #
    @30
    crpss
    wor
    #
    wa
    #
    @34
    @21
    @35
    @30
    @9
    wss
    #
    @29
    vc
    @9
    ssrab2
    @21
    @0
    @9
    cvv
    wcel
    @35
    @39
    wb
    @0
    @19
    @11
    @16
    simp1l
    #
    cA
    cV
    pwexg
    @30
    @9
    cvv
    elpw2g
    3syl
    mpbiri
    @20
    @11
    @16
    simp2
    @21
    @36
    @37
    @21
    @0
    @19
    @14
    @36
    @40
    @32
    @20
    @11
    @14
    @15
    simp3l
    vc
    cA
    @13
    cV
    fin23lem7
    syl3anc
    @16
    @20
    @37
    @11
    @15
    @37
    @14
    vc
    cA
    @13
    sorpsscmpl
    adantl
    3ad2ant3
    #
    jca
    @8
    @38
    @34
    wi
    vy
    @30
    @10
    @2
    @30
    wceq
    #
    @5
    @38
    @7
    @34
    @42
    @3
    @36
    @4
    @37
    @2
    @30
    c0
    neeq1
    @2
    @30
    crpss
    soeq2
    anbi12d
    @42
    @6
    @33
    @2
    @30
    @2
    @30
    inteq
    @42
    id
    eleq12d
    imbi12d
    rspcv
    syl3c
    @21
    @37
    @31
    @34
    wb
    @41
    vw
    vz
    @30
    sorpssint
    syl
    mpbird
    @28
    @24
    cA
    @27
    cdif
    #
    @23
    wpss
    cA
    @23
    cdif
    #
    @27
    wpss
    vz
    vm
    vw
    vn
    cA
    @13
    vc
    @22
    @43
    @23
    psseq1
    @26
    @44
    @27
    psseq1
    @27
    @23
    cA
    pssdifcom1
    fin23lem11
    sylc
    @21
    @15
    @25
    @17
    wb
    @20
    @11
    @14
    @15
    simp3r
    vn
    vm
    @13
    sorpssuni
    syl
    mpbid
    3exp
    sylan2
    ralrimdva
    vb
    cA
    cV
    isfin2
    sylibrd
    impbid2
end
