include "cv.mm"
include "c1st.mm"
include "cid.mm"
include "cres.mm"
include "ccnv.mm"
include "wbr.mm"
include "copab.mm"
include "cop.mm"
include "wceq.mm"
include "cvv.mm"
include "cmpt.mm"
include "vex.mm"
include "brcnv.mm"
include "wcel.mm"
include "wa.mm"
include "brres.mm"
include "wex.mm"
include "cfv.mm"
include "19.42v.mm"
include "op1std.mm"
include "eqeq1d.mm"
include "pm5.32ri.mm"
include "exbii.mm"
include "wfn.mm"
include "wb.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofn.mm"
include "ax-mp.mm"
include "fnbrfvb.mm"
include "mp2an.mm"
include "dfid2.mm"
include "eleq2i.mm"
include "nfe1.mm"
include "19.9.mm"
include "elopab.mm"
include "equid.mm"
include "biantru.mm"
include "3bitr4i.mm"
include "bitr2i.mm"
include "anbi12i.mm"
include "3bitr3ri.mm"
include "id.mm"
include "opeq12d.mm"
include "eqeq2d.mm"
include "ceqsexv.mm"
include "bitri.mm"
include "opabbii.mm"
include "wrel.mm"
include "relcnv.mm"
include "dfrel4v.mm"
include "mpbi.mm"
include "mptv.mm"
include "3eqtr4i.mm"

theorem fsplit
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- `' ( 1st |` _I ) = ( x e. _V |-> <. x , x >. )

  proof
    vx
    cv
    #
    vy
    cv
    #
    c1st
    cid
    cres
    #
    ccnv
    #
    wbr
    #
    vx
    vy
    copab
    #
    @1
    @0
    @0
    cop
    #
    wceq
    #
    vx
    vy
    copab
    @3
    vx
    cvv
    @6
    cmpt
    @4
    @7
    vx
    vy
    @4
    @1
    @0
    @2
    wbr
    #
    @7
    @0
    @1
    @2
    vx
    vex
    #
    vy
    vex
    #
    brcnv
    @8
    @1
    @0
    c1st
    wbr
    #
    @1
    cid
    wcel
    #
    wa
    #
    @7
    @1
    @0
    c1st
    cid
    @9
    brres
    @13
    vz
    cv
    #
    @0
    wceq
    #
    @1
    @14
    @14
    cop
    #
    wceq
    #
    wa
    #
    vz
    wex
    #
    @7
    @1
    c1st
    cfv
    #
    @0
    wceq
    #
    @17
    wa
    #
    vz
    wex
    @21
    @17
    vz
    wex
    #
    wa
    @19
    @13
    @21
    @17
    vz
    19.42v
    @22
    @18
    vz
    @17
    @21
    @15
    @17
    @20
    @14
    @0
    @14
    @14
    @1
    vz
    vex
    #
    @24
    op1std
    eqeq1d
    pm5.32ri
    exbii
    @21
    @11
    @23
    @12
    c1st
    cvv
    wfn
    #
    @1
    cvv
    wcel
    @21
    @11
    wb
    cvv
    cvv
    c1st
    wfo
    @25
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    @10
    cvv
    @1
    @0
    c1st
    fnbrfvb
    mp2an
    @12
    @1
    @14
    @14
    wceq
    #
    vz
    vz
    copab
    #
    wcel
    #
    @23
    cid
    @27
    @1
    vz
    dfid2
    eleq2i
    @17
    @26
    wa
    #
    vz
    wex
    #
    vz
    wex
    @30
    @28
    @23
    @30
    vz
    @29
    vz
    nfe1
    19.9
    @26
    vz
    vz
    @1
    elopab
    @17
    @29
    vz
    @26
    @17
    vz
    equid
    biantru
    exbii
    3bitr4i
    bitr2i
    anbi12i
    3bitr3ri
    @17
    @7
    vz
    @0
    @9
    @15
    @16
    @6
    @1
    @15
    @14
    @0
    @14
    @0
    @15
    id
    #
    @31
    opeq12d
    eqeq2d
    ceqsexv
    bitri
    bitri
    bitri
    opabbii
    @3
    wrel
    @3
    @5
    wceq
    @2
    relcnv
    vx
    vy
    @3
    dfrel4v
    mpbi
    vx
    vy
    @6
    mptv
    3eqtr4i
end
