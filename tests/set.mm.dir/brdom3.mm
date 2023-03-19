include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wmo.mm"
include "wal.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "c0.mm"
include "wceq.mm"
include "wfo.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "csdm.mm"
include "wne.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "reldom.mm"
include "brrelexi.mm"
include "0sdomg.mm"
include "syl.mm"
include "df-ne.mm"
include "syl6bb.mm"
include "biimpar.mm"
include "fodomr.mm"
include "ancoms.mm"
include "syldan.mm"
include "pm5.6.mm"
include "mpbi.mm"
include "br0.mm"
include "nex.mm"
include "exmo.mm"
include "mtpor.mm"
include "ax-gen.mm"
include "rzal.mm"
include "0ex.mm"
include "breq.mm"
include "mobidv.mm"
include "albidv.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcev.mm"
include "sylancr.mm"
include "wfun.mm"
include "fofun.mm"
include "wrel.mm"
include "dffun6.mm"
include "simprbi.mm"
include "wf.mm"
include "dffo4.mm"
include "jca.mm"
include "eximi.mm"
include "jaoi.mm"
include "cxp.mm"
include "cin.mm"
include "cdm.mm"
include "wfn.mm"
include "crn.mm"
include "inss1.mm"
include "ssbri.mm"
include "moimi.mm"
include "alimi.mm"
include "relxp.mm"
include "relin2.mm"
include "ax-mp.mm"
include "mpbiran.mm"
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
include "wss.mm"
include "inss2.mm"
include "dmss.mm"
include "dmxpss.mm"
include "sstri.mm"
include "ssdomg.mm"
include "mp2.mm"
include "domtr.mm"
include "mpan2.mm"
include "3syl.mm"
include "exlimiv.mm"
include "impbii.mm"

theorem brdom3
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
  assert |- ( A ~<_ B <-> E. f ( A. x E* y x f y /\ A. x e. A E. y e. B y f x ) )

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
    wal
    #
    @2
    @1
    @3
    wbr
    #
    vy
    cB
    wrex
    #
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
    cA
    c0
    wceq
    #
    cB
    cA
    @3
    wfo
    #
    vf
    wex
    #
    wo
    #
    @11
    @0
    @12
    wn
    #
    wa
    @14
    wi
    @0
    @15
    wi
    @0
    @16
    c0
    cA
    csdm
    wbr
    #
    @14
    @0
    @17
    @16
    @0
    @17
    cA
    c0
    wne
    #
    @16
    @0
    cA
    cvv
    wcel
    @17
    @18
    wb
    cA
    cB
    cdom
    reldom
    brrelexi
    cA
    cvv
    0sdomg
    syl
    cA
    c0
    df-ne
    syl6bb
    biimpar
    @17
    @0
    @14
    cB
    cA
    vf
    fodomr
    ancoms
    syldan
    @0
    @12
    @14
    pm5.6
    mpbi
    @12
    @11
    @14
    @12
    @1
    @2
    c0
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    #
    @2
    @1
    c0
    wbr
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    @11
    @20
    vx
    @19
    vy
    wex
    @20
    @19
    vy
    @1
    @2
    br0
    nex
    @19
    vy
    exmo
    mtpor
    ax-gen
    @23
    vx
    cA
    rzal
    @10
    @21
    @24
    wa
    vf
    c0
    0ex
    @3
    c0
    wceq
    #
    @6
    @21
    @9
    @24
    @25
    @5
    @20
    vx
    @25
    @4
    @19
    vy
    @1
    @2
    @3
    c0
    breq
    mobidv
    albidv
    @25
    @8
    @23
    vx
    cA
    @25
    @7
    @22
    vy
    cB
    @2
    @1
    @3
    c0
    breq
    rexbidv
    ralbidv
    anbi12d
    spcev
    sylancr
    @13
    @10
    vf
    @13
    @6
    @9
    @13
    @3
    wfun
    #
    @6
    cB
    cA
    @3
    fofun
    @26
    @3
    wrel
    @6
    vx
    vy
    @3
    dffun6
    simprbi
    syl
    @13
    cB
    cA
    @3
    wf
    @9
    vy
    vx
    cB
    cA
    @3
    dffo4
    simprbi
    jca
    eximi
    jaoi
    syl
    @10
    @0
    vf
    @10
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
    @28
    wfo
    #
    cA
    @29
    cdom
    wbr
    #
    @0
    @10
    @28
    @29
    wfn
    #
    @28
    crn
    cA
    wceq
    #
    wa
    @30
    @6
    @32
    @9
    @33
    @6
    @28
    wfun
    #
    @32
    @6
    @1
    @2
    @28
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    #
    @34
    @5
    @36
    vx
    @35
    @4
    vy
    @28
    @3
    @1
    @2
    @3
    @27
    inss1
    ssbri
    moimi
    alimi
    @34
    @28
    wrel
    #
    @37
    @27
    wrel
    @38
    cB
    cA
    relxp
    @3
    @27
    relin2
    ax-mp
    vx
    vy
    @28
    dffun6
    mpbiran
    sylibr
    @28
    funfn
    sylib
    @33
    @9
    vy
    vx
    cB
    cA
    @3
    rninxp
    biimpri
    anim12i
    @29
    cA
    @28
    df-fo
    sylibr
    @29
    cA
    @28
    @28
    @3
    @27
    vf
    vex
    inex1
    dmex
    fodom
    @31
    @29
    cB
    cdom
    wbr
    #
    @0
    cB
    cvv
    wcel
    @29
    cB
    wss
    @39
    brdom3.2
    @29
    @27
    cdm
    #
    cB
    @28
    @27
    wss
    @29
    @40
    wss
    @3
    @27
    inss2
    @28
    @27
    dmss
    ax-mp
    cB
    cA
    dmxpss
    sstri
    @29
    cB
    cvv
    ssdomg
    mp2
    cA
    @29
    cB
    domtr
    mpan2
    3syl
    exlimiv
    impbii
end
