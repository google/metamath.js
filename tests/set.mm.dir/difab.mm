include "cab.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wsb.mm"
include "df-clab.mm"
include "sban.mm"
include "bicomi.mm"
include "sbn.mm"
include "xchbinxr.mm"
include "anbi12i.mm"
include "3bitrri.mm"
include "difeqri.mm"

theorem difab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( { x | ph } \ { x | ps } ) = { x | ( ph /\ -. ps ) }

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
    wn
    #
    wa
    #
    vx
    cab
    #
    vy
    cv
    #
    @4
    wcel
    @3
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    #
    @2
    vx
    vy
    wsb
    #
    wa
    @5
    @0
    wcel
    #
    @5
    @1
    wcel
    #
    wn
    #
    wa
    @3
    vy
    vx
    df-clab
    wph
    @2
    vx
    vy
    sban
    @6
    @8
    @7
    @10
    @8
    @6
    wph
    vy
    vx
    df-clab
    bicomi
    @7
    wps
    vx
    vy
    wsb
    @9
    wps
    vx
    vy
    sbn
    wps
    vy
    vx
    df-clab
    xchbinxr
    anbi12i
    3bitrri
    difeqri
end
