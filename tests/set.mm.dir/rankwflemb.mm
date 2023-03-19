include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "eluni.mm"
include "wceq.mm"
include "wfun.mm"
include "cdm.mm"
include "wlim.mm"
include "r1funlim.mm"
include "simpli.mm"
include "fvelima.mm"
include "mpan.mm"
include "eleq2.mm"
include "biimprcd.mm"
include "wi.mm"
include "cpw.mm"
include "wss.mm"
include "wtr.mm"
include "r1tr.mm"
include "trss.mm"
include "ax-mp.mm"
include "elpwg.mm"
include "mpbird.mm"
include "elfvdm.mm"
include "r1sucg.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "a1i.mm"
include "syl9.mm"
include "reximdvai.mm"
include "syl5.mm"
include "imp.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "crn.mm"
include "fvelrn.mm"
include "sylancr.mm"
include "cres.mm"
include "df-ima.mm"
include "wrel.mm"
include "funrel.mm"
include "word.mm"
include "simpri.mm"
include "limord.mm"
include "ordsson.mm"
include "mp2b.mm"
include "relssres.mm"
include "mp2an.mm"
include "rneqi.mm"
include "eqtri.mm"
include "syl6eleqr.mm"
include "elunii.mm"
include "mpdan.mm"
include "rexlimivw.mm"
include "impbii.mm"

theorem rankwflemb
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. U. ( R1 " On ) <-> E. x e. On A e. ( R1 ` suc x ) )

  proof
    cA
    cr1
    con0
    cima
    #
    cuni
    wcel
    #
    cA
    vx
    cv
    #
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    vx
    con0
    wrex
    #
    @1
    cA
    vy
    cv
    #
    wcel
    #
    @7
    @0
    wcel
    #
    wa
    #
    vy
    wex
    @6
    vy
    cA
    @0
    eluni
    @10
    @6
    vy
    @8
    @9
    @6
    @9
    @2
    cr1
    cfv
    #
    @7
    wceq
    #
    vx
    con0
    wrex
    #
    @8
    @6
    cr1
    wfun
    #
    @9
    @13
    @14
    cr1
    cdm
    #
    wlim
    #
    r1funlim
    simpli
    #
    vx
    @7
    con0
    cr1
    fvelima
    mpan
    @8
    @12
    @5
    vx
    con0
    @8
    @12
    cA
    @11
    wcel
    #
    @2
    con0
    wcel
    #
    @5
    @12
    @18
    @8
    @11
    @7
    cA
    eleq2
    biimprcd
    @18
    @5
    wi
    @19
    @18
    cA
    @11
    cpw
    #
    @4
    @18
    cA
    @20
    wcel
    cA
    @11
    wss
    #
    @11
    wtr
    @18
    @21
    wi
    @2
    r1tr
    @11
    cA
    trss
    ax-mp
    cA
    @11
    @11
    elpwg
    mpbird
    @18
    @2
    @15
    wcel
    @4
    @20
    wceq
    cA
    @2
    cr1
    elfvdm
    @2
    r1sucg
    syl
    eleqtrrd
    a1i
    syl9
    reximdvai
    syl5
    imp
    exlimiv
    sylbi
    @5
    @1
    vx
    con0
    @5
    @4
    @0
    wcel
    @1
    @5
    @4
    cr1
    crn
    #
    @0
    @5
    @14
    @3
    @15
    wcel
    @4
    @22
    wcel
    @17
    cA
    @3
    cr1
    elfvdm
    @3
    cr1
    fvelrn
    sylancr
    @0
    cr1
    con0
    cres
    #
    crn
    @22
    cr1
    con0
    df-ima
    @23
    cr1
    cr1
    wrel
    #
    @15
    con0
    wss
    #
    @23
    cr1
    wceq
    @14
    @24
    @17
    cr1
    funrel
    ax-mp
    @16
    @15
    word
    @25
    @14
    @16
    r1funlim
    simpri
    @15
    limord
    @15
    ordsson
    mp2b
    cr1
    con0
    relssres
    mp2an
    rneqi
    eqtri
    syl6eleqr
    cA
    @4
    @0
    elunii
    mpdan
    rexlimivw
    impbii
end
