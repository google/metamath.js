include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wmo.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "wal.mm"
include "brdom3.mm"
include "alral.mm"
include "anim1i.mm"
include "eximi.mm"
include "sylbi.mm"
include "cxp.mm"
include "cin.mm"
include "cdm.mm"
include "wfo.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "wfun.mm"
include "wrel.mm"
include "wcel.mm"
include "wss.mm"
include "inss2.mm"
include "dmss.mm"
include "ax-mp.mm"
include "dmxpss.mm"
include "sstri.mm"
include "sseli.mm"
include "inss1.mm"
include "ssbri.mm"
include "moimi.mm"
include "imim12i.mm"
include "ralimi2.mm"
include "relxp.mm"
include "relin2.mm"
include "jctil.mm"
include "dffun7.mm"
include "sylibr.mm"
include "funfn.mm"
include "sylib.mm"
include "rninxp.mm"
include "biimpri.mm"
include "anim12i.mm"
include "df-fo.mm"
include "vex.mm"
include "inex1.mm"
include "dmex.mm"
include "fodom.mm"
include "cvv.mm"
include "ssdomg.mm"
include "mp2.mm"
include "domtr.mm"
include "mpan2.mm"
include "3syl.mm"
include "exlimiv.mm"
include "impbii.mm"

theorem brdom5
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  assume brdom3.2: |- B e. _V

  disjoint f x
  disjoint f y
  disjoint A f
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B x
  disjoint B y
  assert |- ( A ~<_ B <-> E. f ( A. x e. B E* y x f y /\ A. x e. A E. y e. B y f x ) )

  proof
    cA
    cB
    cdom
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    vf
    cv
    #
    wbr
    #
    vy
    wmo
    #
    vx
    cB
    wral
    #
    @2
    @1
    @3
    wbr
    vy
    cB
    wrex
    vx
    cA
    wral
    #
    wa
    #
    vf
    wex
    #
    @0
    @5
    vx
    wal
    #
    @7
    wa
    #
    vf
    wex
    @9
    vx
    vy
    cA
    cB
    vf
    brdom3.2
    brdom3
    @11
    @8
    vf
    @10
    @6
    @7
    @5
    vx
    cB
    alral
    anim1i
    eximi
    sylbi
    @8
    @0
    vf
    @8
    @3
    cB
    cA
    cxp
    #
    cin
    #
    cdm
    #
    cA
    @13
    wfo
    #
    cA
    @14
    cdom
    wbr
    #
    @0
    @8
    @13
    @14
    wfn
    #
    @13
    crn
    cA
    wceq
    #
    wa
    @15
    @6
    @17
    @7
    @18
    @6
    @13
    wfun
    #
    @17
    @6
    @13
    wrel
    #
    @1
    @2
    @13
    wbr
    #
    vy
    wmo
    #
    vx
    @14
    wral
    #
    wa
    @19
    @6
    @23
    @20
    @5
    @22
    vx
    cB
    @14
    @1
    @14
    wcel
    @1
    cB
    wcel
    @5
    @22
    @14
    cB
    @1
    @14
    @12
    cdm
    #
    cB
    @13
    @12
    wss
    @14
    @24
    wss
    @3
    @12
    inss2
    @13
    @12
    dmss
    ax-mp
    cB
    cA
    dmxpss
    sstri
    #
    sseli
    @21
    @4
    vy
    @13
    @3
    @1
    @2
    @3
    @12
    inss1
    ssbri
    moimi
    imim12i
    ralimi2
    @12
    wrel
    @20
    cB
    cA
    relxp
    @3
    @12
    relin2
    ax-mp
    jctil
    vx
    vy
    @13
    dffun7
    sylibr
    @13
    funfn
    sylib
    @18
    @7
    vy
    vx
    cB
    cA
    @3
    rninxp
    biimpri
    anim12i
    @14
    cA
    @13
    df-fo
    sylibr
    @14
    cA
    @13
    @13
    @3
    @12
    vf
    vex
    inex1
    dmex
    fodom
    @16
    @14
    cB
    cdom
    wbr
    #
    @0
    cB
    cvv
    wcel
    @14
    cB
    wss
    @26
    brdom3.2
    @25
    @14
    cB
    cvv
    ssdomg
    mp2
    cA
    @14
    cB
    domtr
    mpan2
    3syl
    exlimiv
    impbii
end
