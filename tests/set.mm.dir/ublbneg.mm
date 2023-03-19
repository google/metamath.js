include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cneg.mm"
include "wcel.mm"
include "crab.mm"
include "breq1.mm"
include "cbvralv.mm"
include "rexbii.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "cbvrexv.mm"
include "bitri.mm"
include "renegcl.mm"
include "wa.mm"
include "wi.mm"
include "elrabi.mm"
include "negeq.mm"
include "eleq1d.mm"
include "elrab3.mm"
include "biimpd.mm"
include "mpcom.mm"
include "rspcv.mm"
include "syl.mm"
include "adantl.mm"
include "wb.mm"
include "lenegcon1.mm"
include "sylan2.mm"
include "sylibrd.mm"
include "ralrimdva.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimiv.mm"
include "sylbir.mm"

theorem ublbneg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let va: setvar a
  let vb: setvar b

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b x
  disjoint b y
  disjoint b z
  assert |- ( E. x e. RR A. y e. A y <_ x -> E. x e. RR A. y e. { z e. RR | -u z e. A } x <_ y )

  proof
    vy
    cv
    #
    vx
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
    cr
    wrex
    #
    vb
    cv
    #
    va
    cv
    #
    cle
    wbr
    #
    vb
    cA
    wral
    #
    va
    cr
    wrex
    #
    @1
    @0
    cle
    wbr
    #
    vy
    vz
    cv
    #
    cneg
    #
    cA
    wcel
    #
    vz
    cr
    crab
    #
    wral
    #
    vx
    cr
    wrex
    #
    @9
    @0
    @6
    cle
    wbr
    #
    vy
    cA
    wral
    #
    va
    cr
    wrex
    @4
    @8
    @18
    va
    cr
    @7
    @17
    vb
    vy
    cA
    @5
    @0
    @6
    cle
    breq1
    cbvralv
    rexbii
    @18
    @3
    va
    vx
    cr
    @6
    @1
    wceq
    @17
    @2
    vy
    cA
    @6
    @1
    @0
    cle
    breq2
    ralbidv
    cbvrexv
    bitri
    @8
    @16
    va
    cr
    @6
    cr
    wcel
    #
    @6
    cneg
    #
    cr
    wcel
    @8
    @20
    @0
    cle
    wbr
    #
    vy
    @14
    wral
    #
    @16
    @6
    renegcl
    @19
    @8
    @21
    vy
    @14
    @19
    @0
    @14
    wcel
    #
    wa
    @8
    @0
    cneg
    #
    @6
    cle
    wbr
    #
    @21
    @23
    @8
    @25
    wi
    #
    @19
    @23
    @24
    cA
    wcel
    #
    @26
    @0
    cr
    wcel
    #
    @23
    @27
    @13
    vz
    @0
    cr
    elrabi
    #
    @28
    @23
    @27
    @13
    @27
    vz
    @0
    cr
    @11
    @0
    wceq
    @12
    @24
    cA
    @11
    @0
    negeq
    eleq1d
    elrab3
    biimpd
    mpcom
    @7
    @25
    vb
    @24
    cA
    @5
    @24
    @6
    cle
    breq1
    rspcv
    syl
    adantl
    @23
    @19
    @28
    @21
    @25
    wb
    @29
    @6
    @0
    lenegcon1
    sylan2
    sylibrd
    ralrimdva
    @15
    @22
    vx
    @20
    cr
    @1
    @20
    wceq
    @10
    @21
    vy
    @14
    @1
    @20
    @0
    cle
    breq1
    ralbidv
    rspcev
    syl6an
    rexlimiv
    sylbir
end
