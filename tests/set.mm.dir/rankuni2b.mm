include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "cv.mm"
include "ciun.mm"
include "wral.mm"
include "crab.mm"
include "cint.mm"
include "wceq.mm"
include "uniwf.mm"
include "rankval3b.mm"
include "sylbi.mm"
include "wss.mm"
include "iuneq1.mm"
include "eleq1d.mm"
include "cvv.mm"
include "vex.mm"
include "rankon.mm"
include "rgenw.mm"
include "iunon.mm"
include "mp2an.mm"
include "vtoclg.mm"
include "wrex.mm"
include "eluni2.mm"
include "nfv.mm"
include "nfiu1.mm"
include "nfel2.mm"
include "wi.mm"
include "r1elssi.mm"
include "sseld.mm"
include "rankelb.mm"
include "syl6.mm"
include "ssiun2.mm"
include "a1i.mm"
include "syldd.mm"
include "rexlimd.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "eleq2.mm"
include "ralbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "intss1.mm"
include "syl.mm"
include "eqsstrd.mm"
include "biimpi.mm"
include "elssuni.mm"
include "rankssb.mm"
include "syl2im.mm"
include "iunss.mm"
include "sylibr.mm"
include "eqssd.mm"

theorem rankuni2b
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let cB: class B

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  assert |- ( A e. U. ( R1 " On ) -> ( rank ` U. A ) = U_ x e. A ( rank ` x ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cA
    cuni
    #
    crnk
    cfv
    #
    vx
    cA
    vx
    cv
    #
    crnk
    cfv
    #
    ciun
    #
    @1
    @3
    vy
    cv
    #
    crnk
    cfv
    #
    vz
    cv
    #
    wcel
    #
    vy
    @2
    wral
    #
    vz
    con0
    crab
    #
    cint
    #
    @6
    @1
    @2
    @0
    wcel
    #
    @3
    @13
    wceq
    cA
    uniwf
    #
    vz
    vy
    @2
    rankval3b
    sylbi
    @1
    @6
    @12
    wcel
    #
    @13
    @6
    wss
    @1
    @6
    con0
    wcel
    #
    @8
    @6
    wcel
    #
    vy
    @2
    wral
    #
    @16
    vx
    @7
    @5
    ciun
    #
    con0
    wcel
    #
    @17
    vy
    cA
    @0
    @7
    cA
    wceq
    @20
    @6
    con0
    vx
    @7
    cA
    @5
    iuneq1
    eleq1d
    @7
    cvv
    wcel
    @5
    con0
    wcel
    #
    vx
    @7
    wral
    @21
    vy
    vex
    @22
    vx
    @7
    @4
    rankon
    rgenw
    vx
    @7
    @5
    cvv
    iunon
    mp2an
    vtoclg
    @1
    @18
    vy
    @2
    @7
    @2
    wcel
    @7
    @4
    wcel
    #
    vx
    cA
    wrex
    @1
    @18
    vx
    @7
    cA
    eluni2
    @1
    @23
    @18
    vx
    cA
    @1
    vx
    nfv
    vx
    @8
    @6
    vx
    cA
    @5
    nfiu1
    nfel2
    @1
    @4
    cA
    wcel
    #
    @23
    @8
    @5
    wcel
    #
    @18
    @1
    @24
    @4
    @0
    wcel
    @23
    @25
    wi
    @1
    cA
    @0
    @4
    cA
    r1elssi
    sseld
    @7
    @4
    rankelb
    syl6
    @24
    @25
    @18
    wi
    wi
    @1
    @24
    @5
    @6
    @8
    vx
    cA
    @5
    ssiun2
    sseld
    a1i
    syldd
    rexlimd
    syl5bi
    ralrimiv
    @11
    @19
    vz
    @6
    con0
    @9
    @6
    wceq
    @10
    @18
    vy
    @2
    @9
    @6
    @8
    eleq2
    ralbidv
    elrab
    sylanbrc
    @6
    @12
    intss1
    syl
    eqsstrd
    @1
    @5
    @3
    wss
    #
    vx
    cA
    wral
    @6
    @3
    wss
    @1
    @26
    vx
    cA
    @1
    @14
    @24
    @4
    @2
    wss
    @26
    @1
    @14
    @15
    biimpi
    @4
    cA
    elssuni
    @4
    @2
    rankssb
    syl2im
    ralrimiv
    vx
    cA
    @5
    @3
    iunss
    sylibr
    eqssd
end
