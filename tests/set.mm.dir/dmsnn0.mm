include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "csn.mm"
include "cdm.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "c0.mm"
include "wne.mm"
include "wbr.mm"
include "vex.mm"
include "eldm.mm"
include "df-br.mm"
include "opex.mm"
include "elsn.mm"
include "eqcom.mm"
include "3bitri.mm"
include "exbii.mm"
include "bitr2i.mm"
include "elvv.mm"
include "n0.mm"
include "3bitr4i.mm"

theorem dmsnn0
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. ( _V X. _V ) <-> dom { A } =/= (/) )

  proof
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    vy
    wex
    #
    vx
    wex
    @0
    cA
    csn
    #
    cdm
    #
    wcel
    #
    vx
    wex
    cA
    cvv
    cvv
    cxp
    wcel
    @6
    c0
    wne
    @4
    @7
    vx
    @7
    @0
    @1
    @5
    wbr
    #
    vy
    wex
    @4
    vy
    @0
    @5
    vx
    vex
    eldm
    @8
    @3
    vy
    @8
    @2
    @5
    wcel
    @2
    cA
    wceq
    @3
    @0
    @1
    @5
    df-br
    @2
    cA
    @0
    @1
    opex
    elsn
    @2
    cA
    eqcom
    3bitri
    exbii
    bitr2i
    exbii
    vx
    vy
    cA
    elvv
    vx
    @6
    n0
    3bitr4i
end
