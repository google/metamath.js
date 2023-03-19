include "wel.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "cep.mm"
include "ccom.mm"
include "cdif.mm"
include "crn.mm"
include "wn.mm"
include "wtr.mm"
include "cvv.mm"
include "wbr.mm"
include "wex.mm"
include "elrn.mm"
include "brdif.mm"
include "vex.mm"
include "brco.mm"
include "epel.mm"
include "epelc.mm"
include "anbi12i.mm"
include "exbii.mm"
include "bitri.mm"
include "notbii.mm"
include "19.41v.mm"
include "exanali.mm"
include "bitr3i.mm"
include "3bitri.mm"
include "exnal.mm"
include "con2bii.mm"
include "dftr2.mm"
include "eldif.mm"
include "mpbiran.mm"
include "3bitr4i.mm"

theorem dftr6
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  assume dftr6.1: |- A e. _V


  assert |- ( Tr A <-> A e. ( _V \ ran ( ( _E o. _E ) \ _E ) ) )

  proof
    vx
    vy
    wel
    #
    vy
    cv
    #
    cA
    wcel
    #
    wa
    #
    vx
    cv
    #
    cA
    wcel
    #
    wi
    vy
    wal
    #
    vx
    wal
    #
    cA
    cep
    cep
    ccom
    #
    cep
    cdif
    #
    crn
    #
    wcel
    #
    wn
    #
    cA
    wtr
    cA
    cvv
    @10
    cdif
    wcel
    #
    @11
    @7
    @11
    @4
    cA
    @9
    wbr
    #
    vx
    wex
    @6
    wn
    #
    vx
    wex
    @7
    wn
    vx
    cA
    @9
    dftr6.1
    elrn
    @14
    @15
    vx
    @14
    @4
    cA
    @8
    wbr
    #
    @4
    cA
    cep
    wbr
    #
    wn
    #
    wa
    @3
    vy
    wex
    #
    @5
    wn
    #
    wa
    #
    @15
    @4
    cA
    @8
    cep
    brdif
    @16
    @19
    @18
    @20
    @16
    @4
    @1
    cep
    wbr
    #
    @1
    cA
    cep
    wbr
    #
    wa
    #
    vy
    wex
    @19
    vy
    @4
    cA
    cep
    cep
    vx
    vex
    dftr6.1
    brco
    @24
    @3
    vy
    @22
    @0
    @23
    @2
    vx
    vy
    epel
    @1
    cA
    dftr6.1
    epelc
    anbi12i
    exbii
    bitri
    @17
    @5
    @4
    cA
    dftr6.1
    epelc
    notbii
    anbi12i
    @21
    @3
    @20
    wa
    vy
    wex
    @15
    @3
    @20
    vy
    19.41v
    @3
    @5
    vy
    exanali
    bitr3i
    3bitri
    exbii
    @6
    vx
    exnal
    3bitri
    con2bii
    vx
    vy
    cA
    dftr2
    @13
    cA
    cvv
    wcel
    @12
    dftr6.1
    cA
    cvv
    @10
    eldif
    mpbiran
    3bitr4i
end
