include "cid.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "dfima3.mm"
include "weq.mm"
include "wbr.mm"
include "df-br.mm"
include "vex.mm"
include "ideq.mm"
include "bitr3i.mm"
include "anbi2i.mm"
include "ancom.mm"
include "bitri.mm"
include "exbii.mm"
include "eleq1.mm"
include "equsexvw.mm"
include "abbii.mm"
include "abid2.mm"
include "3eqtri.mm"

theorem imai
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( _I " A ) = A

  proof
    cid
    cA
    cima
    vx
    cv
    #
    cA
    wcel
    #
    @0
    vy
    cv
    #
    cop
    cid
    wcel
    #
    wa
    #
    vx
    wex
    #
    vy
    cab
    @2
    cA
    wcel
    #
    vy
    cab
    cA
    vx
    vy
    cid
    cA
    dfima3
    @5
    @6
    vy
    @5
    vx
    vy
    weq
    #
    @1
    wa
    #
    vx
    wex
    @6
    @4
    @8
    vx
    @4
    @1
    @7
    wa
    @8
    @3
    @7
    @1
    @3
    @0
    @2
    cid
    wbr
    @7
    @0
    @2
    cid
    df-br
    @0
    @2
    vy
    vex
    ideq
    bitr3i
    anbi2i
    @1
    @7
    ancom
    bitri
    exbii
    @1
    @6
    vx
    vy
    @0
    @2
    cA
    eleq1
    equsexvw
    bitri
    abbii
    vy
    cA
    abid2
    3eqtri
end
