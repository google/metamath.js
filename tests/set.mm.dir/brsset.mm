include "csset.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "relsset.mm"
include "brrelexi.mm"
include "ssex.mm"
include "cv.mm"
include "breq1.mm"
include "sseq1.mm"
include "cop.mm"
include "cep.mm"
include "cdif.mm"
include "ctxp.mm"
include "crn.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wa.mm"
include "opex.mm"
include "elrn.mm"
include "vex.mm"
include "brtxp.mm"
include "epel.mm"
include "brv.mm"
include "brdif.mm"
include "mpbiran.mm"
include "epelc.mm"
include "xchbinx.mm"
include "anbi12i.mm"
include "bitri.mm"
include "exbii.mm"
include "exanali.mm"
include "3bitrri.mm"
include "con1bii.mm"
include "df-br.mm"
include "cxp.mm"
include "df-sset.mm"
include "eleq2i.mm"
include "opelvv.mm"
include "eldif.mm"
include "dfss2.mm"
include "3bitr4i.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem brsset
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  assume brsset.1: |- B e. _V


  assert |- ( A SSet B <-> A C_ B )

  proof
    cA
    cB
    csset
    wbr
    #
    cA
    cvv
    wcel
    cA
    cB
    wss
    #
    cA
    cB
    csset
    relsset
    brrelexi
    cA
    cB
    brsset.1
    ssex
    vx
    cv
    #
    cB
    csset
    wbr
    #
    @2
    cB
    wss
    #
    @0
    @1
    vx
    cA
    cvv
    @2
    cA
    cB
    csset
    breq1
    @2
    cA
    cB
    sseq1
    @2
    cB
    cop
    #
    cep
    cvv
    cep
    cdif
    #
    ctxp
    #
    crn
    #
    wcel
    #
    wn
    #
    vy
    cv
    #
    @2
    wcel
    #
    @11
    cB
    wcel
    #
    wi
    vy
    wal
    #
    @3
    @4
    @14
    @9
    @9
    @11
    @5
    @7
    wbr
    #
    vy
    wex
    @12
    @13
    wn
    #
    wa
    #
    vy
    wex
    @14
    wn
    vy
    @5
    @7
    @2
    cB
    opex
    elrn
    @15
    @17
    vy
    @15
    @11
    @2
    cep
    wbr
    #
    @11
    cB
    @6
    wbr
    #
    wa
    @17
    cep
    @6
    @11
    @2
    cB
    vy
    vex
    vx
    vex
    #
    brsset.1
    brtxp
    @18
    @12
    @19
    @16
    vy
    vx
    epel
    @19
    @11
    cB
    cep
    wbr
    #
    @13
    @19
    @11
    cB
    cvv
    wbr
    @21
    wn
    @11
    cB
    brv
    @11
    cB
    cvv
    cep
    brdif
    mpbiran
    @11
    cB
    brsset.1
    epelc
    xchbinx
    anbi12i
    bitri
    exbii
    @12
    @13
    vy
    exanali
    3bitrri
    con1bii
    @3
    @5
    csset
    wcel
    #
    @10
    @2
    cB
    csset
    df-br
    @22
    @5
    cvv
    cvv
    cxp
    #
    @8
    cdif
    #
    wcel
    #
    @10
    csset
    @24
    @5
    df-sset
    eleq2i
    @25
    @5
    @23
    wcel
    @10
    @2
    cB
    @20
    brsset.1
    opelvv
    @5
    @23
    @8
    eldif
    mpbiran
    bitri
    bitri
    vy
    @2
    cB
    dfss2
    3bitr4i
    vtoclbg
    pm5.21nii
end
