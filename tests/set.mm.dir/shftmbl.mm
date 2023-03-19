include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "crab.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "wceq.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "ssrab2.mm"
include "a1i.mm"
include "elpwi.mm"
include "cneg.mm"
include "simpll.mm"
include "simprl.mm"
include "simplr.mm"
include "renegcld.mm"
include "eqidd.mm"
include "ovolshft.mm"
include "simprr.mm"
include "eqeltrrd.mm"
include "mblsplit.mm"
include "syl3anc.mm"
include "inss1.mm"
include "syl5ss.mm"
include "mblss.mm"
include "syl.mm"
include "shft2rab.mm"
include "ineq2d.mm"
include "inrab.mm"
include "elin.mm"
include "rabbii.mm"
include "eqtr4i.mm"
include "syl6eq.mm"
include "ssdifssd.mm"
include "difeq2d.mm"
include "wn.mm"
include "difrab.mm"
include "eldif.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "expr.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "ismbl.mm"
include "sylanbrc.mm"

theorem shftmbl
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( ( A e. dom vol /\ B e. RR ) -> { x e. RR | ( x - B ) e. A } e. dom vol )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    vx
    cv
    cB
    cmin
    co
    cA
    wcel
    #
    vx
    cr
    crab
    #
    cr
    wss
    #
    vy
    cv
    #
    covol
    cfv
    #
    cr
    wcel
    #
    @8
    @7
    @5
    cin
    #
    covol
    cfv
    #
    @7
    @5
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    #
    vy
    cr
    cpw
    #
    wral
    @5
    @0
    wcel
    @6
    @3
    @4
    vx
    cr
    ssrab2
    a1i
    @3
    @16
    vy
    @17
    @7
    @17
    wcel
    @3
    @7
    cr
    wss
    #
    @16
    @7
    cr
    elpwi
    @3
    @18
    @9
    @15
    @3
    @18
    @9
    wa
    #
    wa
    #
    vz
    cv
    cB
    cneg
    #
    cmin
    co
    #
    @7
    wcel
    #
    vz
    cr
    crab
    #
    covol
    cfv
    #
    @24
    cA
    cin
    #
    covol
    cfv
    #
    @24
    cA
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @8
    @14
    @20
    @1
    @24
    cr
    wss
    #
    @25
    cr
    wcel
    @25
    @30
    wceq
    @1
    @2
    @19
    simpll
    #
    @31
    @20
    @23
    vz
    cr
    ssrab2
    a1i
    @20
    @8
    @25
    cr
    @20
    vz
    @7
    @24
    @21
    @3
    @18
    @9
    simprl
    #
    @20
    cB
    @1
    @2
    @19
    simplr
    #
    renegcld
    #
    @20
    @24
    eqidd
    ovolshft
    #
    @3
    @18
    @9
    simprr
    eqeltrrd
    cA
    @24
    mblsplit
    syl3anc
    @36
    @20
    @11
    @27
    @13
    @29
    caddc
    @20
    vz
    @10
    @26
    @21
    @20
    @10
    @7
    cr
    @7
    @5
    inss1
    @33
    syl5ss
    @35
    @20
    @26
    @24
    @22
    @5
    wcel
    #
    vz
    cr
    crab
    #
    cin
    #
    @22
    @10
    wcel
    #
    vz
    cr
    crab
    #
    @20
    cA
    @38
    @24
    @20
    vx
    vz
    cA
    @5
    cB
    @20
    @1
    cA
    cr
    wss
    @32
    cA
    mblss
    syl
    @34
    @20
    @5
    eqidd
    shft2rab
    #
    ineq2d
    @39
    @23
    @37
    wa
    #
    vz
    cr
    crab
    @41
    @23
    @37
    vz
    cr
    inrab
    @40
    @43
    vz
    cr
    @22
    @7
    @5
    elin
    rabbii
    eqtr4i
    syl6eq
    ovolshft
    @20
    vz
    @12
    @28
    @21
    @20
    @7
    cr
    @5
    @33
    ssdifssd
    @35
    @20
    @28
    @24
    @38
    cdif
    #
    @22
    @12
    wcel
    #
    vz
    cr
    crab
    #
    @20
    cA
    @38
    @24
    @42
    difeq2d
    @44
    @23
    @37
    wn
    wa
    #
    vz
    cr
    crab
    @46
    @23
    @37
    vz
    cr
    difrab
    @45
    @47
    vz
    cr
    @22
    @7
    @5
    eldif
    rabbii
    eqtr4i
    syl6eq
    ovolshft
    oveq12d
    3eqtr4d
    expr
    sylan2
    ralrimiva
    vy
    @5
    ismbl
    sylanbrc
end
