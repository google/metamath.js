include "cab.mm"
include "wa.mm"
include "wsb.mm"
include "cv.mm"
include "wcel.mm"
include "sban.mm"
include "df-clab.mm"
include "anbi12i.mm"
include "3bitr4ri.mm"
include "ineqri.mm"

theorem inab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( { x | ph } i^i { x | ps } ) = { x | ( ph /\ ps ) }

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
    wa
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
    wa
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
    wa
    wph
    wps
    vx
    vy
    sban
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
    anbi12i
    3bitr4ri
    ineqri
end
