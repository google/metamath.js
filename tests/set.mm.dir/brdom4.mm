include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wrmo.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "wmo.mm"
include "wal.mm"
include "brdom3.mm"
include "mormo.mm"
include "alimi.mm"
include "alral.mm"
include "syl.mm"
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
include "rnss.mm"
include "rnxpss.mm"
include "inss1.mm"
include "ssbri.mm"
include "anim12i.mm"
include "moimi.mm"
include "df-rmo.mm"
include "3imtr4i.mm"
include "imim12i.mm"
include "ralimi2.mm"
include "relxp.mm"
include "relin2.mm"
include "jctil.mm"
include "dffun9.mm"
include "sylibr.mm"
include "funfn.mm"
include "sylib.mm"
include "rninxp.mm"
include "biimpri.mm"
include "df-fo.mm"
include "vex.mm"
include "inex1.mm"
include "dmex.mm"
include "fodom.mm"
include "cvv.mm"
include "ssdomg.mm"
include "mp2.mm"
include "domtr.mm"
include "sylancl.mm"
include "exlimiv.mm"
include "impbii.mm"

theorem brdom4
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
  assert |- ( A ~<_ B <-> E. f ( A. x e. B E* y e. A x f y /\ A. x e. A E. y e. B y f x ) )

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
    cA
    wrmo
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
    @4
    vy
    wmo
    #
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
    @12
    @8
    vf
    @11
    @6
    @7
    @11
    @5
    vx
    wal
    @6
    @10
    @5
    vx
    @4
    vy
    cA
    mormo
    alimi
    @5
    vx
    cB
    alral
    syl
    anim1i
    eximi
    sylbi
    @8
    @0
    vf
    @8
    cA
    @3
    cB
    cA
    cxp
    #
    cin
    #
    cdm
    #
    cdom
    wbr
    #
    @15
    cB
    cdom
    wbr
    #
    @0
    @8
    @15
    cA
    @14
    wfo
    #
    @16
    @8
    @14
    @15
    wfn
    #
    @14
    crn
    #
    cA
    wceq
    #
    wa
    @18
    @6
    @19
    @7
    @21
    @6
    @14
    wfun
    #
    @19
    @6
    @14
    wrel
    #
    @1
    @2
    @14
    wbr
    #
    vy
    @20
    wrmo
    #
    vx
    @15
    wral
    #
    wa
    @22
    @6
    @26
    @23
    @5
    @25
    vx
    cB
    @15
    @1
    @15
    wcel
    @1
    cB
    wcel
    @5
    @25
    @15
    cB
    @1
    @15
    @13
    cdm
    #
    cB
    @14
    @13
    wss
    #
    @15
    @27
    wss
    @3
    @13
    inss2
    #
    @14
    @13
    dmss
    ax-mp
    cB
    cA
    dmxpss
    sstri
    #
    sseli
    @2
    cA
    wcel
    #
    @4
    wa
    #
    vy
    wmo
    @2
    @20
    wcel
    #
    @24
    wa
    #
    vy
    wmo
    @5
    @25
    @34
    @32
    vy
    @33
    @31
    @24
    @4
    @20
    cA
    @2
    @20
    @13
    crn
    #
    cA
    @28
    @20
    @35
    wss
    @29
    @14
    @13
    rnss
    ax-mp
    cB
    cA
    rnxpss
    sstri
    sseli
    @14
    @3
    @1
    @2
    @3
    @13
    inss1
    ssbri
    anim12i
    moimi
    @4
    vy
    cA
    df-rmo
    @24
    vy
    @20
    df-rmo
    3imtr4i
    imim12i
    ralimi2
    @13
    wrel
    @23
    cB
    cA
    relxp
    @3
    @13
    relin2
    ax-mp
    jctil
    vx
    vy
    @14
    dffun9
    sylibr
    @14
    funfn
    sylib
    @21
    @7
    vy
    vx
    cB
    cA
    @3
    rninxp
    biimpri
    anim12i
    @15
    cA
    @14
    df-fo
    sylibr
    @15
    cA
    @14
    @14
    @3
    @13
    vf
    vex
    inex1
    dmex
    fodom
    syl
    cB
    cvv
    wcel
    @15
    cB
    wss
    @17
    brdom3.2
    @30
    @15
    cB
    cvv
    ssdomg
    mp2
    cA
    @15
    cB
    domtr
    sylancl
    exlimiv
    impbii
end
