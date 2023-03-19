include "wlim.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wcel.mm"
include "ccf.mm"
include "cfv.mm"
include "ccrd.mm"
include "wa.mm"
include "wex.mm"
include "wss.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "wrex.mm"
include "cab.mm"
include "ciin.mm"
include "cflim3.mm"
include "cint.mm"
include "fvex.mm"
include "dfiin2.mm"
include "con0.mm"
include "c0.mm"
include "wne.mm"
include "cardon.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "abssi.mm"
include "limuni.mm"
include "eqcomd.mm"
include "fveq2.mm"
include "biantrud.mm"
include "unieq.mm"
include "eqeq1d.mm"
include "pwid.mm"
include "biantrurd.mm"
include "bitr3d.mm"
include "anbi1d.mm"
include "bitr2d.mm"
include "spcev.mm"
include "syl.mm"
include "df-rex.mm"
include "rabid.mm"
include "anbi1i.mm"
include "exbii.mm"
include "bitri.mm"
include "sylibr.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "abn0.mm"
include "onint.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "eqeltrd.mm"
include "elab.mm"
include "sylib.mm"
include "simprl.mm"
include "simpld.mm"
include "elpwid.mm"
include "simpl.mm"
include "cdm.mm"
include "cvv.mm"
include "vex.mm"
include "word.mm"
include "limord.mm"
include "ordsson.mm"
include "sstr.mm"
include "sylan2.mm"
include "onssnum.mm"
include "cardid2.mm"
include "ensymd.mm"
include "syl2anc.mm"
include "simprr.mm"
include "breqtrrd.mm"
include "simprd.mm"
include "3jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"

theorem cfss
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume cfss.1: |- A e. _V

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( Lim A -> E. x ( x C_ A /\ x ~~ ( cf ` A ) /\ U. x = A ) )

  proof
    cA
    wlim
    #
    vx
    cv
    #
    @1
    cuni
    #
    cA
    wceq
    #
    vx
    cA
    cpw
    #
    crab
    #
    wcel
    #
    cA
    ccf
    cfv
    #
    @1
    ccrd
    cfv
    #
    wceq
    #
    wa
    #
    vx
    wex
    #
    @1
    cA
    wss
    #
    @1
    @7
    cen
    wbr
    #
    @3
    w3a
    #
    vx
    wex
    @0
    @9
    vx
    @5
    wrex
    #
    @11
    @0
    @7
    vy
    cv
    #
    @8
    wceq
    #
    vx
    @5
    wrex
    #
    vy
    cab
    #
    wcel
    @15
    @0
    @7
    vx
    @5
    @8
    ciin
    #
    @19
    vx
    cA
    cfss.1
    cflim3
    @0
    @20
    @19
    cint
    #
    @19
    vx
    vy
    @5
    @8
    @1
    ccrd
    fvex
    dfiin2
    @0
    @19
    con0
    wss
    @19
    c0
    wne
    #
    @21
    @19
    wcel
    @18
    vy
    con0
    @17
    @16
    con0
    wcel
    #
    vx
    @5
    @17
    @23
    @8
    con0
    wcel
    @1
    cardon
    @16
    @8
    con0
    eleq1
    mpbiri
    rexlimivw
    abssi
    @0
    @18
    vy
    wex
    #
    @22
    @0
    cA
    ccrd
    cfv
    #
    @8
    wceq
    #
    vx
    @5
    wrex
    #
    @24
    @0
    @1
    @4
    wcel
    #
    @3
    wa
    #
    @26
    wa
    #
    vx
    wex
    #
    @27
    @0
    cA
    cuni
    #
    cA
    wceq
    #
    @31
    @0
    cA
    @32
    cA
    limuni
    eqcomd
    @30
    @33
    vx
    cA
    cfss.1
    @1
    cA
    wceq
    #
    @33
    @33
    @26
    wa
    @30
    @34
    @26
    @33
    @34
    @8
    @25
    @1
    cA
    ccrd
    fveq2
    eqcomd
    biantrud
    @34
    @33
    @29
    @26
    @34
    @3
    @33
    @29
    @34
    @2
    @32
    cA
    @1
    cA
    unieq
    eqeq1d
    @34
    @28
    @3
    @34
    @28
    cA
    @4
    wcel
    cA
    cfss.1
    pwid
    @1
    cA
    @4
    eleq1
    mpbiri
    biantrurd
    bitr3d
    anbi1d
    bitr2d
    spcev
    syl
    @27
    @6
    @26
    wa
    #
    vx
    wex
    @31
    @26
    vx
    @5
    df-rex
    @35
    @30
    vx
    @6
    @29
    @26
    @3
    vx
    @4
    rabid
    #
    anbi1i
    exbii
    bitri
    sylibr
    @18
    @27
    vy
    @25
    cA
    ccrd
    fvex
    @16
    @25
    wceq
    @17
    @26
    vx
    @5
    @16
    @25
    @8
    eqeq1
    rexbidv
    spcev
    syl
    @18
    vy
    abn0
    sylibr
    @19
    onint
    sylancr
    syl5eqel
    eqeltrd
    @18
    @15
    vy
    @7
    cA
    ccf
    fvex
    @16
    @7
    wceq
    @17
    @9
    vx
    @5
    @16
    @7
    @8
    eqeq1
    rexbidv
    elab
    sylib
    @9
    vx
    @5
    df-rex
    sylib
    @0
    @10
    @14
    vx
    @0
    @10
    @14
    @0
    @10
    wa
    #
    @12
    @13
    @3
    @37
    @1
    cA
    @37
    @28
    @3
    @37
    @6
    @29
    @0
    @6
    @9
    simprl
    @36
    sylib
    #
    simpld
    elpwid
    #
    @37
    @1
    @8
    @7
    cen
    @37
    @12
    @0
    @1
    @8
    cen
    wbr
    @39
    @0
    @10
    simpl
    @12
    @0
    wa
    #
    @8
    @1
    @40
    @1
    ccrd
    cdm
    wcel
    #
    @8
    @1
    cen
    wbr
    @40
    @1
    cvv
    wcel
    @1
    con0
    wss
    #
    @41
    vx
    vex
    @0
    @12
    cA
    con0
    wss
    #
    @42
    @0
    cA
    word
    @43
    cA
    limord
    cA
    ordsson
    syl
    @1
    cA
    con0
    sstr
    sylan2
    @1
    cvv
    onssnum
    sylancr
    @1
    cardid2
    syl
    ensymd
    syl2anc
    @0
    @6
    @9
    simprr
    breqtrrd
    @37
    @28
    @3
    @38
    simprd
    3jca
    ex
    eximdv
    mpd
end
