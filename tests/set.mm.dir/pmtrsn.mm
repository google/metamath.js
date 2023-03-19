include "csn.mm"
include "cpmtr.mm"
include "cfv.mm"
include "cv.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "cpw.mm"
include "crab.mm"
include "wel.mm"
include "cdif.mm"
include "cuni.mm"
include "cif.mm"
include "cmpt.mm"
include "c0.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "snex.mm"
include "eqid.mm"
include "pmtrfval.mm"
include "ax-mp.mm"
include "cdm.mm"
include "dmmpt.mm"
include "wn.mm"
include "wral.mm"
include "cpr.mm"
include "2on0.mm"
include "ensymb.mm"
include "en0.mm"
include "bitri.mm"
include "nemtbir.mm"
include "snnen2o.mm"
include "0ex.mm"
include "breq1.mm"
include "notbid.mm"
include "ralpr.mm"
include "mpbir2an.mm"
include "pwsn.mm"
include "raleqi.mm"
include "mpbir.mm"
include "rabeq0.mm"
include "rabeq.mm"
include "rab0.mm"
include "3eqtri.mm"
include "wrel.mm"
include "wb.mm"
include "wfun.mm"
include "funmpt.mm"
include "funrel.mm"
include "reldm0.mm"
include "eqtri.mm"

theorem pmtrsn
  let cA: class A
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z


  assert |- ( pmTrsp ` { A } ) = (/)

  proof
    cA
    csn
    #
    cpmtr
    cfv
    #
    vp
    vy
    cv
    #
    c2o
    cen
    wbr
    #
    vy
    @0
    cpw
    #
    crab
    #
    vz
    @0
    vz
    vp
    wel
    vp
    cv
    vz
    cv
    #
    csn
    cdif
    cuni
    @6
    cif
    cmpt
    #
    cmpt
    #
    c0
    @0
    cvv
    wcel
    @1
    @8
    wceq
    cA
    snex
    #
    vy
    vz
    @0
    @1
    cvv
    vp
    @1
    eqid
    pmtrfval
    ax-mp
    @8
    c0
    wceq
    #
    @8
    cdm
    #
    c0
    wceq
    #
    @11
    @7
    cvv
    wcel
    #
    vp
    @5
    crab
    #
    @13
    vp
    c0
    crab
    #
    c0
    vp
    @5
    @7
    @8
    @8
    eqid
    dmmpt
    @5
    c0
    wceq
    #
    @14
    @15
    wceq
    @16
    @3
    wn
    #
    vy
    @4
    wral
    #
    @18
    @17
    vy
    c0
    @0
    cpr
    #
    wral
    #
    @20
    c0
    c2o
    cen
    wbr
    #
    wn
    #
    @0
    c2o
    cen
    wbr
    #
    wn
    #
    @21
    c2o
    c0
    2on0
    @21
    c2o
    c0
    cen
    wbr
    c2o
    c0
    wceq
    c0
    c2o
    ensymb
    c2o
    en0
    bitri
    nemtbir
    cA
    snnen2o
    @17
    @22
    @24
    vy
    c0
    @0
    0ex
    @9
    @2
    c0
    wceq
    @3
    @21
    @2
    c0
    c2o
    cen
    breq1
    notbid
    @2
    @0
    wceq
    @3
    @23
    @2
    @0
    c2o
    cen
    breq1
    notbid
    ralpr
    mpbir2an
    @17
    vy
    @4
    @19
    cA
    pwsn
    raleqi
    mpbir
    @3
    vy
    @4
    rabeq0
    mpbir
    @13
    vp
    @5
    c0
    rabeq
    ax-mp
    @13
    vp
    rab0
    3eqtri
    @8
    wrel
    #
    @10
    @12
    wb
    @8
    wfun
    @25
    vp
    @5
    @7
    funmpt
    @8
    funrel
    ax-mp
    @8
    reldm0
    ax-mp
    mpbir
    eqtri
end
