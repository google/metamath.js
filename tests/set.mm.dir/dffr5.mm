include "cv.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cep.mm"
include "ccnv.mm"
include "ccom.mm"
include "crn.mm"
include "wi.mm"
include "wal.mm"
include "wss.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wfr.mm"
include "eldif.mm"
include "selpw.mm"
include "velsn.mm"
include "necon3bbii.mm"
include "anbi12i.mm"
include "bitri.mm"
include "wex.mm"
include "wel.mm"
include "brdif.mm"
include "epel.mm"
include "vex.mm"
include "coep.mm"
include "brcnv.mm"
include "rexbii.mm"
include "dfrex2.mm"
include "3bitrri.mm"
include "con1bii.mm"
include "exbii.mm"
include "elrn.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "imbi12i.mm"
include "albii.mm"
include "dfss2.mm"
include "df-fr.mm"
include "3bitr4ri.mm"

theorem dffr5
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R Fr A <-> ( ~P A \ { (/) } ) C_ ran ( _E \ ( _E o. `' R ) ) )

  proof
    vx
    cv
    #
    cA
    cpw
    #
    c0
    csn
    #
    cdif
    #
    wcel
    #
    @0
    cep
    cep
    cR
    ccnv
    #
    ccom
    #
    cdif
    #
    crn
    #
    wcel
    #
    wi
    #
    vx
    wal
    @0
    cA
    wss
    #
    @0
    c0
    wne
    #
    wa
    #
    vz
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    wn
    vz
    @0
    wral
    #
    vy
    @0
    wrex
    #
    wi
    #
    vx
    wal
    @3
    @8
    wss
    cA
    cR
    wfr
    @10
    @19
    vx
    @4
    @13
    @9
    @18
    @4
    @0
    @1
    wcel
    #
    @0
    @2
    wcel
    #
    wn
    #
    wa
    @13
    @0
    @1
    @2
    eldif
    @20
    @11
    @22
    @12
    vx
    cA
    selpw
    @21
    @0
    c0
    vx
    c0
    velsn
    necon3bbii
    anbi12i
    bitri
    @15
    @0
    @7
    wbr
    #
    vy
    wex
    vy
    vx
    wel
    #
    @17
    wa
    #
    vy
    wex
    @9
    @18
    @23
    @25
    vy
    @23
    @15
    @0
    cep
    wbr
    #
    @15
    @0
    @6
    wbr
    #
    wn
    #
    wa
    @25
    @15
    @0
    cep
    @6
    brdif
    @26
    @24
    @28
    @17
    vy
    vx
    epel
    @17
    @27
    @27
    @15
    @14
    @5
    wbr
    #
    vz
    @0
    wrex
    @16
    vz
    @0
    wrex
    @17
    wn
    vz
    @15
    @0
    @5
    vy
    vex
    #
    vx
    vex
    #
    coep
    @29
    @16
    vz
    @0
    @15
    @14
    cR
    @30
    vz
    vex
    brcnv
    rexbii
    @16
    vz
    @0
    dfrex2
    3bitrri
    con1bii
    anbi12i
    bitri
    exbii
    vy
    @0
    @7
    @31
    elrn
    @17
    vy
    @0
    df-rex
    3bitr4i
    imbi12i
    albii
    vx
    @3
    @8
    dfss2
    vx
    vy
    vz
    cA
    cR
    df-fr
    3bitr4ri
end
