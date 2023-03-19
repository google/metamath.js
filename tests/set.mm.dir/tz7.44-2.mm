include "csuc.mm"
include "wcel.mm"
include "cfv.mm"
include "cres.mm"
include "c0.mm"
include "wceq.mm"
include "cdm.mm"
include "wlim.mm"
include "crn.mm"
include "cuni.mm"
include "cif.mm"
include "cv.mm"
include "fveq2.mm"
include "reseq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "vtoclga.mm"
include "cvv.mm"
include "eleq1d.mm"
include "noel.mm"
include "dmeq.mm"
include "dm0.mm"
include "syl6eq.mm"
include "con0.mm"
include "word.mm"
include "wss.mm"
include "ordsson.mm"
include "ax-mp.mm"
include "wtr.mm"
include "ordtr.mm"
include "trsuc.mm"
include "mpan.mm"
include "sseldi.mm"
include "sucidg.mm"
include "syl.mm"
include "cin.mm"
include "dmres.mm"
include "ordelss.mm"
include "wfn.mm"
include "fndm.mm"
include "syl6sseqr.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "eleqtrrd.mm"
include "eleq2.mm"
include "syl5ibcom.mm"
include "syl5.mm"
include "mtoi.mm"
include "iffalsed.mm"
include "wn.mm"
include "nlimsucg.mm"
include "wb.mm"
include "limeq.mm"
include "mtbird.mm"
include "unieqd.mm"
include "eloni.mm"
include "ordunisuc.mm"
include "eqtrd.mm"
include "fvres.mm"
include "3eqtrd.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "eqeq1.mm"
include "rneq.mm"
include "fveq1.mm"
include "ifbieq12d.mm"
include "ifbieq2d.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem tz7.44-2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  assume tz7.44.1: |- G = ( x e. _V |-> if ( x = (/) , A , if ( Lim dom x , U. ran x , ( H ` ( x ` U. dom x ) ) ) ) )
  assume tz7.44.2: |- ( y e. X -> ( F ` y ) = ( G ` ( F |` y ) ) )
  assume tz7.44.3: |- ( y e. X -> ( F |` y ) e. _V )
  assume tz7.44.4: |- F Fn X
  assume tz7.44.5: |- Ord X

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint G y
  disjoint H x
  disjoint X y
  assert |- ( suc B e. X -> ( F ` suc B ) = ( H ` ( F ` B ) ) )

  proof
    cB
    csuc
    #
    cX
    wcel
    #
    @0
    cF
    cfv
    #
    cF
    @0
    cres
    #
    cG
    cfv
    #
    @3
    c0
    wceq
    #
    cA
    @3
    cdm
    #
    wlim
    #
    @3
    crn
    #
    cuni
    #
    @6
    cuni
    #
    @3
    cfv
    #
    cH
    cfv
    #
    cif
    #
    cif
    #
    cB
    cF
    cfv
    #
    cH
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cF
    @17
    cres
    #
    cG
    cfv
    #
    wceq
    @2
    @4
    wceq
    vy
    @0
    cX
    @17
    @0
    wceq
    #
    @18
    @2
    @20
    @4
    @17
    @0
    cF
    fveq2
    @21
    @19
    @3
    cG
    @17
    @0
    cF
    reseq2
    #
    fveq2d
    eqeq12d
    tz7.44.2
    vtoclga
    @1
    @3
    cvv
    wcel
    #
    @14
    cvv
    wcel
    @4
    @14
    wceq
    @19
    cvv
    wcel
    @23
    vy
    @0
    cX
    @21
    @19
    @3
    cvv
    @22
    eleq1d
    tz7.44.3
    vtoclga
    @1
    @14
    @16
    cvv
    @1
    @14
    @13
    @12
    @16
    @1
    @5
    cA
    @13
    @1
    @5
    cB
    c0
    wcel
    #
    cB
    noel
    @5
    @6
    c0
    wceq
    #
    @1
    @24
    @5
    @6
    c0
    cdm
    c0
    @3
    c0
    dmeq
    dm0
    syl6eq
    @1
    cB
    @6
    wcel
    @25
    @24
    @1
    cB
    @0
    @6
    @1
    cB
    con0
    wcel
    #
    cB
    @0
    wcel
    #
    @1
    cX
    con0
    cB
    cX
    word
    #
    cX
    con0
    wss
    tz7.44.5
    cX
    ordsson
    ax-mp
    cX
    wtr
    #
    @1
    cB
    cX
    wcel
    @28
    @29
    tz7.44.5
    cX
    ordtr
    ax-mp
    cX
    cB
    trsuc
    mpan
    sseldi
    #
    cB
    con0
    sucidg
    syl
    #
    @1
    @6
    @0
    cF
    cdm
    #
    cin
    #
    @0
    cF
    @0
    dmres
    @1
    @0
    @32
    wss
    @33
    @0
    wceq
    @1
    @0
    cX
    @32
    @28
    @1
    @0
    cX
    wss
    tz7.44.5
    cX
    @0
    ordelss
    mpan
    cF
    cX
    wfn
    @32
    cX
    wceq
    tz7.44.4
    cX
    cF
    fndm
    ax-mp
    syl6sseqr
    @0
    @32
    df-ss
    sylib
    syl5eq
    #
    eleqtrrd
    @6
    c0
    cB
    eleq2
    syl5ibcom
    syl5
    mtoi
    iffalsed
    @1
    @7
    @9
    @12
    @1
    @7
    @0
    wlim
    #
    @1
    @26
    @35
    wn
    @30
    cB
    con0
    nlimsucg
    syl
    @1
    @6
    @0
    wceq
    @7
    @35
    wb
    @34
    @6
    @0
    limeq
    syl
    mtbird
    iffalsed
    @1
    @11
    @15
    cH
    @1
    @11
    cB
    @3
    cfv
    #
    @15
    @1
    @10
    cB
    @3
    @1
    @10
    @0
    cuni
    #
    cB
    @1
    @6
    @0
    @34
    unieqd
    @1
    @26
    @37
    cB
    wceq
    #
    @30
    @26
    cB
    word
    @38
    cB
    eloni
    cB
    ordunisuc
    syl
    syl
    eqtrd
    fveq2d
    @1
    @27
    @36
    @15
    wceq
    @31
    cB
    @0
    cF
    fvres
    syl
    eqtrd
    fveq2d
    3eqtrd
    #
    @15
    cH
    fvex
    syl6eqel
    vx
    @3
    vx
    cv
    #
    c0
    wceq
    #
    cA
    @40
    cdm
    #
    wlim
    #
    @40
    crn
    #
    cuni
    #
    @42
    cuni
    #
    @40
    cfv
    #
    cH
    cfv
    #
    cif
    #
    cif
    @14
    cvv
    cvv
    cG
    @40
    @3
    wceq
    #
    @41
    @5
    @49
    @13
    cA
    @40
    @3
    c0
    eqeq1
    @50
    @43
    @7
    @45
    @48
    @9
    @12
    @50
    @42
    @6
    wceq
    @43
    @7
    wb
    @40
    @3
    dmeq
    #
    @42
    @6
    limeq
    syl
    @50
    @44
    @8
    @40
    @3
    rneq
    unieqd
    @50
    @47
    @11
    cH
    @50
    @47
    @46
    @3
    cfv
    @11
    @46
    @40
    @3
    fveq1
    @50
    @46
    @10
    @3
    @50
    @42
    @6
    @51
    unieqd
    fveq2d
    eqtrd
    fveq2d
    ifbieq12d
    ifbieq2d
    tz7.44.1
    fvmptg
    syl2anc
    @39
    3eqtrd
end
