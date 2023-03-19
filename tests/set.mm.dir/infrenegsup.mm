include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "clt.mm"
include "cinf.mm"
include "cneg.mm"
include "wcel.mm"
include "crab.mm"
include "csup.mm"
include "infrecl.mm"
include "recnd.mm"
include "negnegd.mm"
include "ccnv.mm"
include "cmpt.mm"
include "cfv.mm"
include "cima.mm"
include "negeq.mm"
include "cbvmptv.mm"
include "mptpreima.mm"
include "wiso.mm"
include "wceq.mm"
include "eqid.mm"
include "negiso.mm"
include "simpri.mm"
include "imaeq1i.mm"
include "eqtr3i.mm"
include "supeq1i.mm"
include "simpli.mm"
include "isocnv.mm"
include "ax-mp.mm"
include "wb.mm"
include "isoeq1.mm"
include "mpbi.mm"
include "a1i.mm"
include "simp1.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "infm3.mm"
include "vex.mm"
include "brcnv.mm"
include "notbii.mm"
include "ralbii.mm"
include "rexbii.mm"
include "imbi12i.mm"
include "anbi12i.mm"
include "sylibr.mm"
include "wor.mm"
include "gtso.mm"
include "supiso.mm"
include "syl5eq.mm"
include "df-inf.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "negex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqtr2d.mm"
include "negeqd.mm"
include "eqtr3d.mm"

theorem infrenegsup
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A x <_ y ) -> inf ( A , RR , < ) = -u sup ( { z e. RR | -u z e. A } , RR , < ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    w3a
    #
    cA
    cr
    clt
    cinf
    #
    cneg
    #
    cneg
    @6
    vz
    cv
    #
    cneg
    #
    cA
    wcel
    vz
    cr
    crab
    #
    cr
    clt
    csup
    #
    cneg
    @5
    @6
    @5
    @6
    vx
    vy
    cA
    infrecl
    #
    recnd
    negnegd
    @5
    @7
    @11
    @5
    @11
    cA
    cr
    clt
    ccnv
    #
    csup
    #
    vw
    cr
    vw
    cv
    #
    cneg
    #
    cmpt
    #
    cfv
    #
    @7
    @5
    @11
    @17
    cA
    cima
    #
    cr
    clt
    csup
    @18
    cr
    @10
    @19
    clt
    @17
    ccnv
    #
    cA
    cima
    @10
    @19
    vz
    cr
    @9
    cA
    @17
    vw
    vz
    cr
    @16
    @9
    @15
    @8
    negeq
    cbvmptv
    mptpreima
    @20
    @17
    cA
    cr
    cr
    clt
    @13
    @17
    wiso
    #
    @20
    @17
    wceq
    #
    vw
    @17
    @17
    eqid
    #
    negiso
    #
    simpri
    #
    imaeq1i
    eqtr3i
    supeq1i
    @5
    vx
    vy
    vz
    cr
    cr
    cA
    @13
    clt
    @17
    cr
    cr
    @13
    clt
    @17
    wiso
    #
    @5
    cr
    cr
    @13
    clt
    @20
    wiso
    #
    @26
    @21
    @27
    @21
    @22
    @24
    simpli
    cr
    cr
    clt
    @13
    @17
    isocnv
    ax-mp
    @22
    @27
    @26
    wb
    @25
    cr
    cr
    @13
    clt
    @17
    @20
    isoeq1
    ax-mp
    mpbi
    a1i
    @0
    @1
    @4
    simp1
    @5
    @3
    @2
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @2
    @3
    clt
    wbr
    #
    @8
    @3
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cr
    wral
    #
    wa
    #
    vx
    cr
    wrex
    @2
    @3
    @13
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @3
    @2
    @13
    wbr
    #
    @3
    @8
    @13
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cr
    wral
    #
    wa
    #
    vx
    cr
    wrex
    vx
    vy
    vz
    cA
    infm3
    @45
    @36
    vx
    cr
    @39
    @30
    @44
    @35
    @38
    @29
    vy
    cA
    @37
    @28
    @2
    @3
    clt
    vx
    vex
    #
    vy
    vex
    #
    brcnv
    notbii
    ralbii
    @43
    @34
    vy
    cr
    @40
    @31
    @42
    @33
    @3
    @2
    clt
    @47
    @46
    brcnv
    @41
    @32
    vz
    cA
    @3
    @8
    clt
    @47
    vz
    vex
    brcnv
    rexbii
    imbi12i
    ralbii
    anbi12i
    rexbii
    sylibr
    cr
    @13
    wor
    @5
    gtso
    a1i
    supiso
    syl5eq
    @5
    @6
    cr
    wcel
    #
    @18
    @7
    wceq
    @12
    @48
    @18
    @6
    @17
    cfv
    @7
    @14
    @6
    @17
    @6
    @14
    cA
    cr
    clt
    df-inf
    eqcomi
    fveq2i
    vw
    @6
    @16
    @7
    cr
    @17
    @15
    @6
    negeq
    @23
    @6
    negex
    fvmpt
    syl5eq
    syl
    eqtr2d
    negeqd
    eqtr3d
end
