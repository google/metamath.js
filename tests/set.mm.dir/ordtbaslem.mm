include "ctsr.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "cfi.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "wa.mm"
include "cif.mm"
include "wo.mm"
include "wb.mm"
include "w3a.mm"
include "3anrot.mm"
include "tsrlemax.mm"
include "sylan2br.mm"
include "3exp2.mm"
include "imp42.mm"
include "notbid.mm"
include "ioran.mm"
include "syl6bb.mm"
include "rabbidva.mm"
include "cvv.mm"
include "ifcl.mm"
include "ancoms.mm"
include "adantl.mm"
include "cdm.mm"
include "dmexg.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "rabexg.mm"
include "syl.mm"
include "eqeltrd.mm"
include "eqid.mm"
include "breq2.mm"
include "rabbidv.mm"
include "elrnmpt1s.mm"
include "syl6eleqr.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "ralrimivva.mm"
include "ralrimivw.mm"
include "cbvmptv.mm"
include "ineq1.mm"
include "inrab.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "ralrnmpt.mm"
include "mpbird.mm"
include "ineq2.mm"
include "raleqi.mm"
include "raleqbii.mm"
include "sylibr.mm"
include "cpw.mm"
include "pwexg.mm"
include "wf.mm"
include "wss.mm"
include "ssrab2.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "fmptd.mm"
include "frn.mm"
include "syl5eqss.mm"
include "ssexd.mm"
include "inficl.mm"
include "mpbid.mm"

theorem ordtbaslem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cV: class V
  assume ordtval.1: |- X = dom R
  assume ordtval.2: |- A = ran ( x e. X |-> { y e. X | -. y R x } )

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint a w
  disjoint a z
  disjoint A a
  disjoint b m
  disjoint b n
  disjoint b r
  disjoint b w
  disjoint b z
  disjoint A b
  disjoint m n
  disjoint m r
  disjoint m w
  disjoint m z
  disjoint A m
  disjoint n r
  disjoint n w
  disjoint n z
  disjoint A n
  disjoint r w
  disjoint r z
  disjoint A r
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint a x
  disjoint a y
  disjoint R a
  disjoint b x
  disjoint b y
  disjoint R b
  disjoint m x
  disjoint m y
  disjoint R m
  disjoint n x
  disjoint n y
  disjoint R n
  disjoint r x
  disjoint r y
  disjoint R r
  disjoint w x
  disjoint w y
  disjoint R w
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint X a
  disjoint X b
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X w
  disjoint X z
  disjoint B a
  disjoint B b
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint B z
  disjoint C m
  disjoint C n
  disjoint C z
  disjoint V x
  assert |- ( R e. TosetRel -> ( fi ` A ) = A )

  proof
    cR
    ctsr
    wcel
    #
    vz
    cv
    #
    vw
    cv
    #
    cin
    #
    cA
    wcel
    #
    vw
    cA
    wral
    #
    vz
    cA
    wral
    #
    cA
    cfi
    cfv
    cA
    wceq
    #
    @0
    @4
    vw
    vx
    cX
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cX
    crab
    #
    cmpt
    #
    crn
    #
    wral
    #
    vz
    @14
    wral
    #
    @6
    @0
    @16
    @1
    @8
    vb
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cX
    crab
    #
    cin
    #
    cA
    wcel
    #
    vb
    cX
    wral
    #
    vz
    @14
    wral
    #
    @0
    @24
    @8
    va
    cv
    #
    cR
    wbr
    #
    wn
    #
    @19
    wa
    #
    vy
    cX
    crab
    #
    cA
    wcel
    #
    vb
    cX
    wral
    #
    va
    cX
    wral
    #
    @0
    @30
    va
    vb
    cX
    cX
    @0
    @25
    cX
    wcel
    #
    @17
    cX
    wcel
    #
    wa
    #
    wa
    #
    @8
    @25
    @17
    cR
    wbr
    #
    @17
    @25
    cif
    #
    cR
    wbr
    #
    wn
    #
    vy
    cX
    crab
    #
    @29
    cA
    @36
    @40
    @28
    vy
    cX
    @36
    @8
    cX
    wcel
    #
    wa
    #
    @40
    @26
    @18
    wo
    #
    wn
    @28
    @43
    @39
    @44
    @0
    @33
    @34
    @42
    @39
    @44
    wb
    #
    @0
    @33
    @34
    @42
    @45
    @33
    @34
    @42
    w3a
    @0
    @42
    @33
    @34
    w3a
    @45
    @42
    @33
    @34
    3anrot
    @8
    @25
    @17
    cR
    cX
    ordtval.1
    tsrlemax
    sylan2br
    3exp2
    imp42
    notbid
    @26
    @18
    ioran
    syl6bb
    rabbidva
    #
    @36
    @38
    cX
    wcel
    #
    @41
    cvv
    wcel
    #
    @41
    cA
    wcel
    @35
    @47
    @0
    @34
    @33
    @47
    @37
    @17
    @25
    cX
    ifcl
    ancoms
    adantl
    @36
    @41
    @29
    cvv
    @46
    @36
    cX
    cvv
    wcel
    #
    @29
    cvv
    wcel
    @0
    @49
    @35
    @0
    cX
    cR
    cdm
    cvv
    ordtval.1
    cR
    ctsr
    dmexg
    syl5eqel
    #
    adantr
    @28
    vy
    cX
    cvv
    rabexg
    syl
    eqeltrd
    @47
    @48
    wa
    @41
    @14
    cA
    vx
    cX
    @12
    @41
    @38
    @13
    cvv
    @13
    eqid
    #
    @9
    @38
    wceq
    #
    @11
    @40
    vy
    cX
    @52
    @10
    @39
    @9
    @38
    @8
    cR
    breq2
    notbid
    rabbidv
    elrnmpt1s
    ordtval.2
    syl6eleqr
    syl2anc
    eqeltrrd
    ralrimivva
    @0
    @27
    vy
    cX
    crab
    #
    cvv
    wcel
    #
    va
    cX
    wral
    @24
    @32
    wb
    @0
    @54
    va
    cX
    @0
    @49
    @54
    @50
    @27
    vy
    cX
    cvv
    rabexg
    syl
    ralrimivw
    @23
    @31
    va
    vz
    cX
    @53
    @13
    cvv
    vx
    va
    cX
    @12
    @53
    @9
    @25
    wceq
    #
    @11
    @27
    vy
    cX
    @55
    @10
    @26
    @9
    @25
    @8
    cR
    breq2
    notbid
    rabbidv
    cbvmptv
    @1
    @53
    wceq
    #
    @22
    @30
    vb
    cX
    @56
    @21
    @29
    cA
    @56
    @21
    @53
    @20
    cin
    @29
    @1
    @53
    @20
    ineq1
    @27
    @19
    vy
    cX
    inrab
    syl6eq
    eleq1d
    ralbidv
    ralrnmpt
    syl
    mpbird
    @0
    @15
    @23
    vz
    @14
    @0
    @20
    cvv
    wcel
    #
    vb
    cX
    wral
    @15
    @23
    wb
    @0
    @57
    vb
    cX
    @0
    @49
    @57
    @50
    @19
    vy
    cX
    cvv
    rabexg
    syl
    ralrimivw
    @4
    @22
    vb
    vw
    cX
    @20
    @13
    cvv
    vx
    vb
    cX
    @12
    @20
    @9
    @17
    wceq
    #
    @11
    @19
    vy
    cX
    @58
    @10
    @18
    @9
    @17
    @8
    cR
    breq2
    notbid
    rabbidv
    cbvmptv
    @2
    @20
    wceq
    @3
    @21
    cA
    @2
    @20
    @1
    ineq2
    eleq1d
    ralrnmpt
    syl
    ralbidv
    mpbird
    @5
    @15
    vz
    cA
    @14
    ordtval.2
    @4
    vw
    cA
    @14
    ordtval.2
    raleqi
    raleqbii
    sylibr
    @0
    cA
    cvv
    wcel
    @6
    @7
    wb
    @0
    cA
    cX
    cpw
    #
    cvv
    @0
    @49
    @59
    cvv
    wcel
    @50
    cX
    cvv
    pwexg
    syl
    @0
    cA
    @14
    @59
    ordtval.2
    @0
    cX
    @59
    @13
    wf
    @14
    @59
    wss
    @0
    vx
    cX
    @12
    @59
    @13
    @0
    @9
    cX
    wcel
    #
    wa
    #
    @12
    @59
    wcel
    #
    @12
    cX
    wss
    #
    @11
    vy
    cX
    ssrab2
    @61
    @49
    @62
    @63
    wb
    @0
    @49
    @60
    @50
    adantr
    @12
    cX
    cvv
    elpw2g
    syl
    mpbiri
    @51
    fmptd
    cX
    @59
    @13
    frn
    syl
    syl5eqss
    ssexd
    vz
    vw
    cA
    cvv
    inficl
    syl
    mpbid
end
