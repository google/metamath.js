include "cdm.mm"
include "wcel.mm"
include "cvv.mm"
include "csn.mm"
include "cres.mm"
include "c0.mm"
include "wne.mm"
include "elex.mm"
include "wn.mm"
include "wceq.mm"
include "snprc.mm"
include "reseq2.mm"
include "res0.mm"
include "syl6eq.mm"
include "sylbi.mm"
include "necon1ai.mm"
include "cv.mm"
include "eleq1.mm"
include "sneq.mm"
include "reseq2d.mm"
include "neeq1d.mm"
include "cop.mm"
include "wex.mm"
include "wa.mm"
include "df-clel.mm"
include "exbii.mm"
include "vex.mm"
include "eldm2.mm"
include "n0.mm"
include "wrex.mm"
include "elres.mm"
include "weq.mm"
include "pm5.32i.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "syl5bbr.mm"
include "exbidv.mm"
include "rexsn.mm"
include "bitri.mm"
include "excom.mm"
include "3bitri.mm"
include "3bitr4i.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem eldm3
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vp: setvar p


  assert |- ( A e. dom B <-> ( B |` { A } ) =/= (/) )

  proof
    cA
    cB
    cdm
    #
    wcel
    #
    cA
    cvv
    wcel
    #
    cB
    cA
    csn
    #
    cres
    #
    c0
    wne
    #
    cA
    @0
    elex
    @2
    @4
    c0
    @2
    wn
    @3
    c0
    wceq
    #
    @4
    c0
    wceq
    cA
    snprc
    @6
    @4
    cB
    c0
    cres
    c0
    @3
    c0
    cB
    reseq2
    cB
    res0
    syl6eq
    sylbi
    necon1ai
    vx
    cv
    #
    @0
    wcel
    #
    cB
    @7
    csn
    #
    cres
    #
    c0
    wne
    #
    @1
    @5
    vx
    cA
    cvv
    @7
    cA
    @0
    eleq1
    @7
    cA
    wceq
    #
    @10
    @4
    c0
    @12
    @9
    @3
    cB
    @7
    cA
    sneq
    reseq2d
    neeq1d
    @7
    vy
    cv
    #
    cop
    #
    cB
    wcel
    #
    vy
    wex
    vp
    cv
    #
    @14
    wceq
    #
    @16
    cB
    wcel
    #
    wa
    #
    vp
    wex
    #
    vy
    wex
    #
    @8
    @11
    @15
    @20
    vy
    vp
    @14
    cB
    df-clel
    exbii
    vy
    @7
    cB
    vx
    vex
    #
    eldm2
    @11
    @16
    @10
    wcel
    #
    vp
    wex
    @19
    vy
    wex
    #
    vp
    wex
    @21
    vp
    @10
    n0
    @23
    @24
    vp
    @23
    @16
    vz
    cv
    #
    @13
    cop
    #
    wceq
    #
    @26
    cB
    wcel
    #
    wa
    #
    vy
    wex
    #
    vz
    @9
    wrex
    @24
    vz
    vy
    @16
    cB
    @9
    elres
    @30
    @24
    vz
    @7
    @22
    vz
    vx
    weq
    #
    @29
    @19
    vy
    @29
    @27
    @18
    wa
    @31
    @19
    @27
    @18
    @28
    @16
    @26
    cB
    eleq1
    pm5.32i
    @31
    @27
    @17
    @18
    @31
    @26
    @14
    @16
    @25
    @7
    @13
    opeq1
    eqeq2d
    anbi1d
    syl5bbr
    exbidv
    rexsn
    bitri
    exbii
    @19
    vp
    vy
    excom
    3bitri
    3bitr4i
    vtoclbg
    pm5.21nii
end
