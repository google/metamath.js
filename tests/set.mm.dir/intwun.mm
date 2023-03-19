include "cwun.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cint.mm"
include "wcel.mm"
include "wtr.mm"
include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "w3a.mm"
include "simpl.mm"
include "sselda.mm"
include "wuntr.mm"
include "syl.mm"
include "ralrimiva.mm"
include "trint.mm"
include "wun0.mm"
include "0ex.mm"
include "elint2.mm"
include "sylibr.mm"
include "ne0i.mm"
include "adantlr.mm"
include "intss1.mm"
include "adantl.mm"
include "an32s.mm"
include "wununi.mm"
include "vuniex.mm"
include "wunpw.mm"
include "vpwex.mm"
include "wunpr.mm"
include "prex.mm"
include "3jca.mm"
include "cvv.mm"
include "wb.mm"
include "simpr.mm"
include "intex.mm"
include "sylib.mm"
include "iswun.mm"
include "mpbir3and.mm"

theorem intwun
  let cA: class A
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A C_ WUni /\ A =/= (/) ) -> |^| A e. WUni )

  proof
    cA
    cwun
    wss
    #
    cA
    c0
    wne
    #
    wa
    #
    cA
    cint
    #
    cwun
    wcel
    #
    @3
    wtr
    #
    @3
    c0
    wne
    #
    vx
    cv
    #
    cuni
    #
    @3
    wcel
    #
    @7
    cpw
    #
    @3
    wcel
    #
    @7
    vy
    cv
    #
    cpr
    #
    @3
    wcel
    #
    vy
    @3
    wral
    #
    w3a
    #
    vx
    @3
    wral
    #
    @2
    vu
    cv
    #
    wtr
    #
    vu
    cA
    wral
    @5
    @2
    @19
    vu
    cA
    @2
    @18
    cA
    wcel
    #
    wa
    #
    @18
    cwun
    wcel
    #
    @19
    @2
    cA
    cwun
    @18
    @0
    @1
    simpl
    sselda
    #
    @18
    wuntr
    syl
    ralrimiva
    vu
    cA
    trint
    syl
    @2
    c0
    @3
    wcel
    #
    @6
    @2
    c0
    @18
    wcel
    #
    vu
    cA
    wral
    @24
    @2
    @25
    vu
    cA
    @21
    @18
    @23
    wun0
    ralrimiva
    vu
    c0
    cA
    0ex
    elint2
    sylibr
    @3
    c0
    ne0i
    syl
    @2
    @16
    vx
    @3
    @2
    @7
    @3
    wcel
    #
    wa
    #
    @9
    @11
    @15
    @27
    @8
    @18
    wcel
    #
    vu
    cA
    wral
    @9
    @27
    @28
    vu
    cA
    @27
    @20
    wa
    #
    @7
    @18
    @2
    @20
    @22
    @26
    @23
    adantlr
    #
    @2
    @20
    @26
    @7
    @18
    wcel
    #
    @21
    @3
    @18
    @7
    @20
    @3
    @18
    wss
    #
    @2
    @18
    cA
    intss1
    #
    adantl
    sselda
    an32s
    #
    wununi
    ralrimiva
    vu
    @8
    cA
    vx
    vuniex
    elint2
    sylibr
    @27
    @10
    @18
    wcel
    #
    vu
    cA
    wral
    @11
    @27
    @35
    vu
    cA
    @29
    @7
    @18
    @30
    @34
    wunpw
    ralrimiva
    vu
    @10
    cA
    vx
    vpwex
    elint2
    sylibr
    @27
    @14
    vy
    @3
    @27
    @12
    @3
    wcel
    #
    wa
    #
    @13
    @18
    wcel
    #
    vu
    cA
    wral
    @14
    @37
    @38
    vu
    cA
    @37
    @20
    wa
    @7
    @12
    @18
    @27
    @20
    @22
    @36
    @30
    adantlr
    @27
    @20
    @31
    @36
    @34
    adantlr
    @27
    @20
    @36
    @12
    @18
    wcel
    @29
    @3
    @18
    @12
    @20
    @32
    @27
    @33
    adantl
    sselda
    an32s
    wunpr
    ralrimiva
    vu
    @13
    cA
    @7
    @12
    prex
    elint2
    sylibr
    ralrimiva
    3jca
    ralrimiva
    @2
    @3
    cvv
    wcel
    #
    @4
    @5
    @6
    @17
    w3a
    wb
    @2
    @1
    @39
    @0
    @1
    simpr
    cA
    intex
    sylib
    vx
    vy
    @3
    cvv
    iswun
    syl
    mpbir3and
end
