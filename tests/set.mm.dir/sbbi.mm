include "wb.mm"
include "wsb.mm"
include "wi.mm"
include "wa.mm"
include "dfbi2.mm"
include "sbbii.mm"
include "sbim.mm"
include "anbi12i.mm"
include "sban.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem sbbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] ( ph <-> ps ) <-> ( [ y / x ] ph <-> [ y / x ] ps ) )

  proof
    wph
    wps
    wb
    #
    vx
    vy
    wsb
    wph
    wps
    wi
    #
    wps
    wph
    wi
    #
    wa
    #
    vx
    vy
    wsb
    #
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
    wb
    #
    @0
    @3
    vx
    vy
    wph
    wps
    dfbi2
    sbbii
    @1
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
    @6
    wi
    #
    @6
    @5
    wi
    #
    wa
    @4
    @7
    @8
    @10
    @9
    @11
    wph
    wps
    vx
    vy
    sbim
    wps
    wph
    vx
    vy
    sbim
    anbi12i
    @1
    @2
    vx
    vy
    sban
    @5
    @6
    dfbi2
    3bitr4i
    bitri
end
