include "con0.mm"
include "wcel.mm"
include "cmade.mm"
include "cfv.mm"
include "cscut.mm"
include "cima.mm"
include "cuni.mm"
include "cpw.mm"
include "cxp.mm"
include "cv.mm"
include "csslt.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "csur.mm"
include "crab.mm"
include "madeval.mm"
include "cab.mm"
include "csn.mm"
include "scutcut.mm"
include "simp1d.mm"
include "eleq1.mm"
include "biimpd.mm"
include "mpan9.mm"
include "rexlimivw.mm"
include "pm4.71ri.mm"
include "abbii.mm"
include "cop.mm"
include "breq1.mm"
include "anbi12d.mm"
include "rexxp.mm"
include "cin.mm"
include "cdm.mm"
include "imaindm.mm"
include "dmscut.mm"
include "ineq2i.mm"
include "imaeq2i.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "vex.mm"
include "elima.mm"
include "elin.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "rexbii2.mm"
include "3bitri.mm"
include "df-br.mm"
include "df-ov.mm"
include "eqeq1i.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "scutf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnbrfvb.mm"
include "mpan.mm"
include "syl5bb.mm"
include "pm5.32i.mm"
include "2rexbii.mm"
include "3bitr4i.mm"
include "abbi2i.mm"
include "df-rab.mm"
include "3eqtr4i.mm"
include "syl6eq.mm"

theorem madeval2
  let vx: setvar x
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vy: setvar y

  disjoint A x
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint A y
  disjoint a y
  disjoint b y
  disjoint x y
  assert |- ( A e. On -> ( _M ` A ) = { x e. No | E. a e. ~P U. ( _M " A ) E. b e. ~P U. ( _M " A ) ( a <<s b /\ ( a |s b ) = x ) } )

  proof
    cA
    con0
    wcel
    cA
    cmade
    cfv
    cscut
    cmade
    cA
    cima
    cuni
    cpw
    #
    @0
    cxp
    #
    cima
    #
    va
    cv
    #
    vb
    cv
    #
    csslt
    wbr
    #
    @3
    @4
    cscut
    co
    #
    vx
    cv
    #
    wceq
    #
    wa
    #
    vb
    @0
    wrex
    #
    va
    @0
    wrex
    #
    vx
    csur
    crab
    #
    cA
    madeval
    @11
    vx
    cab
    @7
    csur
    wcel
    #
    @11
    wa
    #
    vx
    cab
    @2
    @12
    @11
    @14
    vx
    @11
    @13
    @10
    @13
    va
    @0
    @9
    @13
    vb
    @0
    @5
    @6
    csur
    wcel
    #
    @8
    @13
    @5
    @15
    @3
    @6
    csn
    #
    csslt
    wbr
    @16
    @4
    csslt
    wbr
    @3
    @4
    scutcut
    simp1d
    @8
    @15
    @13
    @6
    @7
    csur
    eleq1
    biimpd
    mpan9
    rexlimivw
    rexlimivw
    pm4.71ri
    abbii
    @11
    vx
    @2
    vy
    cv
    #
    csslt
    wcel
    #
    @17
    @7
    cscut
    wbr
    #
    wa
    #
    vy
    @1
    wrex
    #
    @3
    @4
    cop
    #
    csslt
    wcel
    #
    @22
    @7
    cscut
    wbr
    #
    wa
    #
    vb
    @0
    wrex
    va
    @0
    wrex
    @7
    @2
    wcel
    #
    @11
    @20
    @25
    vy
    va
    vb
    @0
    @0
    @17
    @22
    wceq
    @18
    @23
    @19
    @24
    @17
    @22
    csslt
    eleq1
    @17
    @22
    @7
    cscut
    breq1
    anbi12d
    rexxp
    @26
    @7
    cscut
    @1
    csslt
    cin
    #
    cima
    #
    wcel
    @19
    vy
    @27
    wrex
    @21
    @2
    @28
    @7
    @2
    cscut
    @1
    cscut
    cdm
    #
    cin
    #
    cima
    @28
    @1
    cscut
    imaindm
    @30
    @27
    cscut
    @29
    csslt
    @1
    dmscut
    ineq2i
    imaeq2i
    eqtri
    eleq2i
    vy
    @7
    cscut
    @27
    vx
    vex
    elima
    @19
    @20
    vy
    @27
    @1
    @17
    @27
    wcel
    #
    @19
    wa
    @17
    @1
    wcel
    #
    @18
    wa
    #
    @19
    wa
    @32
    @20
    wa
    @31
    @33
    @19
    @17
    @1
    csslt
    elin
    anbi1i
    @32
    @18
    @19
    anass
    bitri
    rexbii2
    3bitri
    @9
    @25
    va
    vb
    @0
    @0
    @9
    @23
    @8
    wa
    @25
    @5
    @23
    @8
    @3
    @4
    csslt
    df-br
    anbi1i
    @23
    @8
    @24
    @8
    @22
    cscut
    cfv
    #
    @7
    wceq
    #
    @23
    @24
    @6
    @34
    @7
    @3
    @4
    cscut
    df-ov
    eqeq1i
    cscut
    csslt
    wfn
    #
    @23
    @35
    @24
    wb
    csslt
    csur
    cscut
    wf
    @36
    scutf
    csslt
    csur
    cscut
    ffn
    ax-mp
    csslt
    @22
    @7
    cscut
    fnbrfvb
    mpan
    syl5bb
    pm5.32i
    bitri
    2rexbii
    3bitr4i
    abbi2i
    @11
    vx
    csur
    df-rab
    3eqtr4i
    syl6eq
end
