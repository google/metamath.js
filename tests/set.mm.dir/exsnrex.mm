include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "vsnid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "pm4.71ri.mm"
include "exbii.mm"
include "df-rex.mm"
include "bitr4i.mm"

theorem exsnrex
  let vx: setvar x
  let cM: class M


  assert |- ( E. x M = { x } <-> E. x e. M M = { x } )

  proof
    cM
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    wex
    @0
    cM
    wcel
    #
    @2
    wa
    #
    vx
    wex
    @2
    vx
    cM
    wrex
    @2
    @4
    vx
    @2
    @3
    @2
    @3
    @0
    @1
    wcel
    vx
    vsnid
    cM
    @1
    @0
    eleq2
    mpbiri
    pm4.71ri
    exbii
    @2
    vx
    cM
    df-rex
    bitr4i
end
