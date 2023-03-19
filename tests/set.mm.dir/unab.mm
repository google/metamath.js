include "cab.mm"
include "wo.mm"
include "wsb.mm"
include "cv.mm"
include "wcel.mm"
include "sbor.mm"
include "df-clab.mm"
include "orbi12i.mm"
include "3bitr4ri.mm"
include "uneqri.mm"

theorem unab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( { x | ph } u. { x | ps } ) = { x | ( ph \/ ps ) }

  proof
    vy
    wph
    vx
    cab
    #
    wps
    vx
    cab
    #
    wph
    wps
    wo
    #
    vx
    cab
    #
    @2
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    #
    wps
    vx
    vy
    wsb
    #
    wo
    vy
    cv
    #
    @3
    wcel
    @6
    @0
    wcel
    #
    @6
    @1
    wcel
    #
    wo
    wph
    wps
    vx
    vy
    sbor
    @2
    vy
    vx
    df-clab
    @7
    @4
    @8
    @5
    wph
    vy
    vx
    df-clab
    wps
    vy
    vx
    df-clab
    orbi12i
    3bitr4ri
    uneqri
end
