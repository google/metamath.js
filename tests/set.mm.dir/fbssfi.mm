include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "cfi.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "cuni.mm"
include "cpw.mm"
include "crab.mm"
include "cin.mm"
include "wral.mm"
include "cab.mm"
include "cint.mm"
include "dffi2.mm"
include "wi.mm"
include "w3a.mm"
include "inss1.mm"
include "simp1r.mm"
include "elpwid.mm"
include "syl5ss.mm"
include "vex.mm"
include "inex1.mm"
include "elpw.mm"
include "sylibr.mm"
include "simpl.mm"
include "fbasssin.mm"
include "syl3an.mm"
include "ss2in.mm"
include "ad2ant2l.mm"
include "3adant1.mm"
include "sstr.mm"
include "expcom.mm"
include "syl.mm"
include "reximdv.mm"
include "mpd.mm"
include "wceq.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "3expa.mm"
include "rexlimdvaa.mm"
include "ralrimivw.mm"
include "sseq1.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "ralrab.mm"
include "ralrimiva.mm"
include "pwuni.mm"
include "ssid.mm"
include "rspcev.mm"
include "mpan2.mm"
include "rgen.mm"
include "ssrab.mm"
include "mpbir2an.mm"
include "jctil.mm"
include "cvv.mm"
include "wb.mm"
include "uniexg.mm"
include "pwexg.mm"
include "rabexg.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "elabg.mm"
include "4syl.mm"
include "mpbird.mm"
include "intss1.mm"
include "eqsstrd.mm"
include "sselda.mm"
include "simprbi.mm"

theorem fbssfi
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cX: class X
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint F x
  disjoint X x
  disjoint t x
  disjoint A t
  disjoint t u
  disjoint t v
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint X u
  disjoint X v
  disjoint X y
  disjoint X z
  assert |- ( ( F e. ( fBas ` X ) /\ A e. ( fi ` F ) ) -> E. x e. F x C_ A )

  proof
    cF
    cX
    cfbas
    cfv
    #
    wcel
    #
    cA
    cF
    cfi
    cfv
    #
    wcel
    wa
    cA
    vx
    cv
    #
    vt
    cv
    #
    wss
    #
    vx
    cF
    wrex
    #
    vt
    cF
    cuni
    #
    cpw
    #
    crab
    #
    wcel
    #
    @3
    cA
    wss
    #
    vx
    cF
    wrex
    #
    @1
    @2
    @9
    cA
    @1
    @2
    cF
    vz
    cv
    #
    wss
    #
    vu
    cv
    #
    vv
    cv
    #
    cin
    #
    @13
    wcel
    #
    vv
    @13
    wral
    #
    vu
    @13
    wral
    #
    wa
    #
    vz
    cab
    #
    cint
    #
    @9
    vu
    vv
    vz
    cF
    @0
    dffi2
    @1
    @9
    @22
    wcel
    #
    @23
    @9
    wss
    @1
    @24
    cF
    @9
    wss
    #
    @17
    @9
    wcel
    #
    vv
    @9
    wral
    #
    vu
    @9
    wral
    #
    wa
    #
    @1
    @28
    @25
    @1
    vy
    cv
    #
    @15
    wss
    #
    vy
    cF
    wrex
    #
    @27
    wi
    #
    vu
    @8
    wral
    @28
    @1
    @33
    vu
    @8
    @1
    @15
    @8
    wcel
    #
    wa
    #
    @31
    @27
    vy
    cF
    @35
    @30
    cF
    wcel
    #
    @31
    wa
    #
    wa
    #
    @13
    @16
    wss
    #
    vz
    cF
    wrex
    #
    @26
    wi
    #
    vv
    @8
    wral
    @27
    @38
    @41
    vv
    @8
    @38
    @39
    @26
    vz
    cF
    @35
    @37
    @13
    cF
    wcel
    #
    @39
    wa
    #
    @26
    @35
    @37
    @43
    w3a
    #
    @17
    @8
    wcel
    #
    @3
    @17
    wss
    #
    vx
    cF
    wrex
    #
    @26
    @44
    @17
    @7
    wss
    @45
    @44
    @17
    @15
    @7
    @15
    @16
    inss1
    @44
    @15
    @7
    @1
    @34
    @37
    @43
    simp1r
    elpwid
    syl5ss
    @17
    @7
    @15
    @16
    vu
    vex
    inex1
    elpw
    sylibr
    @44
    @3
    @30
    @13
    cin
    #
    wss
    #
    vx
    cF
    wrex
    #
    @47
    @35
    @1
    @37
    @36
    @43
    @42
    @50
    @1
    @34
    simpl
    @36
    @31
    simpl
    @42
    @39
    simpl
    vx
    @30
    @13
    cF
    cX
    fbasssin
    syl3an
    @44
    @49
    @46
    vx
    cF
    @44
    @48
    @17
    wss
    #
    @49
    @46
    wi
    @37
    @43
    @51
    @35
    @31
    @39
    @51
    @36
    @42
    @30
    @15
    @13
    @16
    ss2in
    ad2ant2l
    3adant1
    @49
    @51
    @46
    @3
    @48
    @17
    sstr
    expcom
    syl
    reximdv
    mpd
    @6
    @47
    vt
    @17
    @8
    @4
    @17
    wceq
    @5
    @46
    vx
    cF
    @4
    @17
    @3
    sseq2
    rexbidv
    elrab
    sylanbrc
    3expa
    rexlimdvaa
    ralrimivw
    @6
    @40
    @26
    vv
    vt
    @8
    @4
    @16
    wceq
    #
    @6
    @3
    @16
    wss
    #
    vx
    cF
    wrex
    @40
    @52
    @5
    @53
    vx
    cF
    @4
    @16
    @3
    sseq2
    rexbidv
    @53
    @39
    vx
    vz
    cF
    @3
    @13
    @16
    sseq1
    cbvrexv
    syl6bb
    ralrab
    sylibr
    rexlimdvaa
    ralrimiva
    @6
    @32
    @27
    vu
    vt
    @8
    @4
    @15
    wceq
    #
    @6
    @3
    @15
    wss
    #
    vx
    cF
    wrex
    @32
    @54
    @5
    @55
    vx
    cF
    @4
    @15
    @3
    sseq2
    rexbidv
    @55
    @31
    vx
    vy
    cF
    @3
    @30
    @15
    sseq1
    cbvrexv
    syl6bb
    ralrab
    sylibr
    @25
    cF
    @8
    wss
    @6
    vt
    cF
    wral
    cF
    pwuni
    @6
    vt
    cF
    @4
    cF
    wcel
    @4
    @4
    wss
    #
    @6
    @4
    ssid
    @5
    @56
    vx
    @4
    cF
    @3
    @4
    @4
    sseq1
    rspcev
    mpan2
    rgen
    @6
    vt
    @8
    cF
    ssrab
    mpbir2an
    jctil
    @1
    @7
    cvv
    wcel
    @8
    cvv
    wcel
    @9
    cvv
    wcel
    @24
    @29
    wb
    cF
    @0
    uniexg
    @7
    cvv
    pwexg
    @6
    vt
    @8
    cvv
    rabexg
    @21
    @29
    vz
    @9
    cvv
    @13
    @9
    wceq
    @14
    @25
    @20
    @28
    @13
    @9
    cF
    sseq2
    @19
    @27
    vu
    @13
    @9
    @18
    @26
    vv
    @13
    @9
    @13
    @9
    @17
    eleq2
    raleqbi1dv
    raleqbi1dv
    anbi12d
    elabg
    4syl
    mpbird
    @9
    @22
    intss1
    syl
    eqsstrd
    sselda
    @10
    cA
    @8
    wcel
    @12
    @6
    @12
    vt
    cA
    @8
    @4
    cA
    wceq
    @5
    @11
    vx
    cF
    @4
    cA
    @3
    sseq2
    rexbidv
    elrab
    simprbi
    syl
end
