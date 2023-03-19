include "csur.mm"
include "wss.mm"
include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wa.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "cbday.mm"
include "cfv.mm"
include "cima.mm"
include "cint.mm"
include "wceq.mm"
include "wn.mm"
include "w3a.mm"
include "wrex.mm"
include "breq1.mm"
include "anbi1d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "breq2.mm"
include "anbi2d.mm"
include "rspc2v.mm"
include "weq.mm"
include "anbi12d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "cdm.mm"
include "bdaydm.mm"
include "sseq2i.mm"
include "wfun.mm"
include "bdayfun.mm"
include "funfvima2.mm"
include "mpan.mm"
include "sylbir.mm"
include "imp.mm"
include "intss1.mm"
include "syl.mm"
include "con0.mm"
include "wb.mm"
include "c0.mm"
include "wne.mm"
include "crn.mm"
include "imassrn.mm"
include "bdayrn.mm"
include "sseqtri.mm"
include "ne0i.mm"
include "oninton.mm"
include "sylancr.mm"
include "bdayelon.mm"
include "ontri1.mm"
include "sylancl.mm"
include "mpbid.mm"
include "ex.mm"
include "eleq2.mm"
include "notbid.mm"
include "biimprcd.mm"
include "syl6.mm"
include "com3l.mm"
include "adantrd.mm"
include "syl8.mm"
include "com35.mm"
include "com4l.mm"
include "impcom.mm"
include "imp42.mm"
include "con2d.mm"
include "3anass.mm"
include "notbii.mm"
include "imnan.mm"
include "bitr4i.mm"
include "sylibr.mm"
include "nrexdv.mm"
include "ssel.mm"
include "anim12d.mm"
include "eqtr3.mm"
include "anim12i.mm"
include "anasss.mm"
include "adantlr.mm"
include "nodense.mm"
include "anassrs.mm"
include "sylan.mm"
include "mtand.mm"

theorem nocvxminlem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cX: class X
  let cY: class Y
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y y
  disjoint Y z
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint X w
  disjoint Y w
  assert |- ( ( A C_ No /\ A. x e. A A. y e. A A. z e. No ( ( x <s z /\ z <s y ) -> z e. A ) ) -> ( ( ( X e. A /\ Y e. A ) /\ ( ( bday ` X ) = |^| ( bday " A ) /\ ( bday ` Y ) = |^| ( bday " A ) ) ) -> -. X <s Y ) )

  proof
    cA
    csur
    wss
    #
    vx
    cv
    #
    vz
    cv
    #
    cslt
    wbr
    #
    @2
    vy
    cv
    #
    cslt
    wbr
    #
    wa
    #
    @2
    cA
    wcel
    #
    wi
    #
    vz
    csur
    wral
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    #
    cX
    cA
    wcel
    #
    cY
    cA
    wcel
    #
    wa
    #
    cX
    cbday
    cfv
    #
    cbday
    cA
    cima
    #
    cint
    #
    wceq
    #
    cY
    cbday
    cfv
    #
    @17
    wceq
    #
    wa
    #
    wa
    #
    cX
    cY
    cslt
    wbr
    #
    wn
    @11
    @22
    wa
    #
    @23
    vw
    cv
    #
    cbday
    cfv
    #
    @15
    wcel
    #
    cX
    @25
    cslt
    wbr
    #
    @25
    cY
    cslt
    wbr
    #
    w3a
    #
    vw
    csur
    wrex
    #
    @24
    @30
    vw
    csur
    @24
    @25
    csur
    wcel
    #
    wa
    #
    @27
    @28
    @29
    wa
    #
    wn
    wi
    #
    @30
    wn
    #
    @33
    @34
    @27
    @11
    @14
    @21
    @32
    @34
    @27
    wn
    #
    wi
    #
    @10
    @0
    @14
    @21
    @32
    @38
    wi
    wi
    #
    wi
    @14
    @10
    @0
    @39
    @14
    @10
    cX
    @2
    cslt
    wbr
    #
    @2
    cY
    cslt
    wbr
    #
    wa
    #
    @7
    wi
    #
    vz
    csur
    wral
    #
    @0
    @39
    wi
    @9
    @44
    @40
    @5
    wa
    #
    @7
    wi
    #
    vz
    csur
    wral
    vx
    vy
    cX
    cY
    cA
    cA
    @1
    cX
    wceq
    #
    @8
    @46
    vz
    csur
    @47
    @6
    @45
    @7
    @47
    @3
    @40
    @5
    @1
    cX
    @2
    cslt
    breq1
    anbi1d
    imbi1d
    ralbidv
    @4
    cY
    wceq
    #
    @46
    @43
    vz
    csur
    @48
    @45
    @42
    @7
    @48
    @5
    @41
    @40
    @4
    cY
    @2
    cslt
    breq2
    anbi2d
    imbi1d
    ralbidv
    rspc2v
    @32
    @44
    @0
    @21
    @38
    @32
    @44
    @34
    @21
    @0
    @37
    @32
    @44
    @34
    @25
    cA
    wcel
    #
    @21
    @0
    @37
    wi
    #
    wi
    @43
    @34
    @49
    wi
    vz
    @25
    csur
    vz
    vw
    weq
    #
    @42
    @34
    @7
    @49
    @51
    @40
    @28
    @41
    @29
    @2
    @25
    cX
    cslt
    breq2
    @2
    @25
    cY
    cslt
    breq1
    anbi12d
    @2
    @25
    cA
    eleq1
    imbi12d
    rspcv
    @49
    @18
    @50
    @20
    @0
    @49
    @18
    @37
    @0
    @49
    @26
    @17
    wcel
    #
    wn
    #
    @18
    @37
    wi
    @0
    @49
    @53
    @0
    @49
    wa
    #
    @17
    @26
    wss
    #
    @53
    @54
    @26
    @16
    wcel
    #
    @55
    @0
    @49
    @56
    @0
    cA
    cbday
    cdm
    #
    wss
    #
    @49
    @56
    wi
    #
    @57
    csur
    cA
    bdaydm
    sseq2i
    cbday
    wfun
    @58
    @59
    bdayfun
    cA
    @25
    cbday
    funfvima2
    mpan
    sylbir
    imp
    #
    @26
    @16
    intss1
    syl
    @54
    @17
    con0
    wcel
    #
    @26
    con0
    wcel
    @55
    @53
    wb
    @54
    @16
    con0
    wss
    @16
    c0
    wne
    #
    @61
    @16
    cbday
    crn
    con0
    cbday
    cA
    imassrn
    bdayrn
    sseqtri
    @54
    @56
    @62
    @60
    @16
    @26
    ne0i
    syl
    @16
    oninton
    sylancr
    @25
    bdayelon
    @17
    @26
    ontri1
    sylancl
    mpbid
    ex
    @18
    @37
    @53
    @18
    @27
    @52
    @15
    @17
    @26
    eleq2
    notbid
    biimprcd
    syl6
    com3l
    adantrd
    syl8
    com35
    com4l
    syl6
    com3l
    impcom
    imp42
    con2d
    @36
    @27
    @34
    wa
    #
    wn
    @35
    @30
    @63
    @27
    @28
    @29
    3anass
    notbii
    @27
    @34
    imnan
    bitr4i
    sylibr
    nrexdv
    @24
    cX
    csur
    wcel
    #
    cY
    csur
    wcel
    #
    wa
    #
    @15
    @19
    wceq
    #
    wa
    #
    @23
    @31
    @0
    @22
    @68
    @10
    @0
    @14
    @21
    @68
    @0
    @14
    wa
    @66
    @21
    @67
    @0
    @14
    @66
    @0
    @12
    @64
    @13
    @65
    cA
    csur
    cX
    ssel
    cA
    csur
    cY
    ssel
    anim12d
    imp
    @15
    @19
    @17
    eqtr3
    anim12i
    anasss
    adantlr
    @66
    @67
    @23
    @31
    vw
    cX
    cY
    nodense
    anassrs
    sylan
    mtand
    ex
end
