include "c1.mm"
include "c2.mm"
include "cpr.mm"
include "cpmtr.mm"
include "cfv.mm"
include "crn.mm"
include "csn.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "cop.mm"
include "pmtrprfval.mm"
include "rneqi.mm"
include "wrex.mm"
include "cab.mm"
include "eqid.mm"
include "rnmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "1ex.mm"
include "cn.mm"
include "id.mm"
include "2nn.mm"
include "a1i.mm"
include "iftrue.mm"
include "adantl.mm"
include "1ne2.mm"
include "nesymi.mm"
include "eqeq1.mm"
include "mtbiri.mm"
include "iffalsed.mm"
include "fmptpr.mm"
include "eqeq2d.mm"
include "ax-mp.mm"
include "bicomi.mm"
include "rexbii.mm"
include "abbii.mm"
include "c0.mm"
include "wne.mm"
include "prex.mm"
include "snnz.mm"
include "r19.9rzv.mm"
include "bicomd.mm"
include "vex.mm"
include "weq.mm"
include "rexbidv.mm"
include "elab.mm"
include "velsn.mm"
include "3bitr4i.mm"
include "eqriv.mm"
include "eqtri.mm"

theorem pmtrprfvalrn
  let vp: setvar p
  let vt: setvar t
  let vz: setvar z
  let vs: setvar s


  assert |- ran ( pmTrsp ` { 1 , 2 } ) = { { <. 1 , 2 >. , <. 2 , 1 >. } }

  proof
    c1
    c2
    cpr
    #
    cpmtr
    cfv
    #
    crn
    vp
    @0
    csn
    #
    vz
    @0
    vz
    cv
    #
    c1
    wceq
    #
    c2
    c1
    cif
    #
    cmpt
    #
    cmpt
    #
    crn
    #
    c1
    c2
    cop
    c2
    c1
    cop
    cpr
    #
    csn
    #
    @1
    @7
    vz
    vp
    pmtrprfval
    rneqi
    @8
    vt
    cv
    #
    @6
    wceq
    #
    vp
    @2
    wrex
    #
    vt
    cab
    #
    @10
    vp
    vt
    @2
    @6
    @7
    @7
    eqid
    rnmpt
    @14
    @11
    @9
    wceq
    #
    vp
    @2
    wrex
    #
    vt
    cab
    #
    @10
    @13
    @16
    vt
    @12
    @15
    vp
    @2
    @15
    @12
    c1
    cvv
    wcel
    #
    @15
    @12
    wb
    1ex
    @18
    @9
    @6
    @11
    @18
    vz
    c1
    c2
    c2
    c1
    @5
    cvv
    cn
    cn
    cvv
    @18
    id
    #
    c2
    cn
    wcel
    @18
    2nn
    a1i
    #
    @20
    @19
    @4
    @5
    c2
    wceq
    @18
    @4
    c2
    c1
    iftrue
    adantl
    @3
    c2
    wceq
    #
    @5
    c1
    wceq
    @18
    @21
    @4
    c2
    c1
    @21
    @4
    c2
    c1
    wceq
    c1
    c2
    1ne2
    nesymi
    @3
    c2
    c1
    eqeq1
    mtbiri
    iffalsed
    adantl
    fmptpr
    eqeq2d
    ax-mp
    bicomi
    rexbii
    abbii
    vs
    @17
    @10
    vs
    cv
    #
    @9
    wceq
    #
    vp
    @2
    wrex
    #
    @23
    @22
    @17
    wcel
    @22
    @10
    wcel
    @2
    c0
    wne
    #
    @24
    @23
    wb
    @0
    c1
    c2
    prex
    snnz
    @25
    @23
    @24
    @23
    vp
    @2
    r19.9rzv
    bicomd
    ax-mp
    @16
    @24
    vt
    @22
    vs
    vex
    vt
    vs
    weq
    @15
    @23
    vp
    @2
    @11
    @22
    @9
    eqeq1
    rexbidv
    elab
    vs
    @9
    velsn
    3bitr4i
    eqriv
    eqtri
    eqtri
    eqtri
end
