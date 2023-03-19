include "cr.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "crab.mm"
include "wral.mm"
include "wrex.mm"
include "ssrab2.mm"
include "a1i.mm"
include "negfi.mm"
include "3adant3.mm"
include "negn0.mm"
include "3adant2.mm"
include "fimaxre.mm"
include "syl3anc.mm"
include "wi.mm"
include "wa.mm"
include "weq.mm"
include "negeq.mm"
include "eleq1d.mm"
include "elrab.mm"
include "simpllr.mm"
include "wceq.mm"
include "wb.mm"
include "breq1.mm"
include "ralbidv.mm"
include "adantl.mm"
include "ssel.mm"
include "renegcl.mm"
include "syl6.mm"
include "imp.mm"
include "cc.mm"
include "recn.mm"
include "negnegd.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "sylanbrc.mm"
include "rspcv.mm"
include "syl.mm"
include "simplll.mm"
include "lenegcon1.mm"
include "syl2anc.mm"
include "sylibd.mm"
include "impancom.mm"
include "ralrimiv.mm"
include "rspcedvd.mm"
include "ex.mm"
include "sylbi.mm"
include "impcom.mm"
include "rexlimdva.mm"
include "3ad2ant1.mm"
include "mpd.mm"

theorem fiminre
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A m
  disjoint A n
  disjoint A r
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint r x
  disjoint r y
  assert |- ( ( A C_ RR /\ A e. Fin /\ A =/= (/) ) -> E. x e. A A. y e. A x <_ y )

  proof
    cA
    cr
    wss
    #
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    w3a
    #
    vm
    cv
    #
    vn
    cv
    #
    cle
    wbr
    #
    vm
    vr
    cv
    #
    cneg
    #
    cA
    wcel
    #
    vr
    cr
    crab
    #
    wral
    #
    vn
    @10
    wrex
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @3
    @10
    cr
    wss
    #
    @10
    cfn
    wcel
    #
    @10
    c0
    wne
    #
    @12
    @18
    @3
    @9
    vr
    cr
    ssrab2
    a1i
    @0
    @1
    @19
    @2
    cA
    vr
    negfi
    3adant3
    @0
    @2
    @20
    @1
    vr
    cA
    negn0
    3adant2
    vn
    vm
    @10
    fimaxre
    syl3anc
    @0
    @1
    @12
    @17
    wi
    @2
    @0
    @11
    @17
    vn
    @10
    @5
    @10
    wcel
    #
    @0
    @11
    @17
    wi
    #
    @21
    @5
    cr
    wcel
    #
    @5
    cneg
    #
    cA
    wcel
    #
    wa
    #
    @0
    @22
    wi
    @9
    @25
    vr
    @5
    cr
    vr
    vn
    weq
    @8
    @24
    cA
    @7
    @5
    negeq
    eleq1d
    elrab
    @26
    @0
    @22
    @26
    @0
    wa
    #
    @11
    @17
    @27
    @11
    wa
    #
    @16
    @24
    @14
    cle
    wbr
    #
    vy
    cA
    wral
    #
    vx
    @24
    cA
    @23
    @25
    @0
    @11
    simpllr
    @13
    @24
    wceq
    #
    @16
    @30
    wb
    @28
    @31
    @15
    @29
    vy
    cA
    @13
    @24
    @14
    cle
    breq1
    ralbidv
    adantl
    @28
    @29
    vy
    cA
    @27
    @14
    cA
    wcel
    #
    @11
    @29
    @27
    @32
    wa
    #
    @11
    @14
    cneg
    #
    @5
    cle
    wbr
    #
    @29
    @33
    @34
    @10
    wcel
    #
    @11
    @35
    wi
    @33
    @34
    cr
    wcel
    #
    @34
    cneg
    #
    cA
    wcel
    #
    @36
    @27
    @32
    @37
    @0
    @32
    @37
    wi
    @26
    @0
    @32
    @14
    cr
    wcel
    #
    @37
    cA
    cr
    @14
    ssel
    #
    @14
    renegcl
    syl6
    adantl
    imp
    @33
    @38
    @14
    cA
    @33
    @14
    @27
    @32
    @14
    cc
    wcel
    #
    @27
    @32
    @40
    @42
    @0
    @32
    @40
    wi
    @26
    @41
    adantl
    #
    @14
    recn
    syl6
    imp
    negnegd
    @27
    @32
    simpr
    eqeltrd
    @9
    @39
    vr
    @34
    cr
    @7
    @34
    wceq
    @8
    @38
    cA
    @7
    @34
    negeq
    eleq1d
    elrab
    sylanbrc
    @6
    @35
    vm
    @34
    @10
    @4
    @34
    @5
    cle
    breq1
    rspcv
    syl
    @33
    @40
    @23
    @35
    @29
    wb
    @27
    @32
    @40
    @43
    imp
    @23
    @25
    @0
    @32
    simplll
    @14
    @5
    lenegcon1
    syl2anc
    sylibd
    impancom
    ralrimiv
    rspcedvd
    ex
    ex
    sylbi
    impcom
    rexlimdva
    3ad2ant1
    mpd
end
