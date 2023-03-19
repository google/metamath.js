include "wn.mm"
include "wi.mm"
include "wsb.mm"
include "wo.mm"
include "sbim.mm"
include "sbn.mm"
include "imbi1i.mm"
include "bitri.mm"
include "df-or.mm"
include "sbbii.mm"
include "3bitr4i.mm"

theorem sbor
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y


  assert |- ( [ y / x ] ( ph \/ ps ) <-> ( [ y / x ] ph \/ [ y / x ] ps ) )

  proof
    wph
    wn
    #
    wps
    wi
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
    wn
    #
    wps
    vx
    vy
    wsb
    #
    wi
    #
    wph
    wps
    wo
    #
    vx
    vy
    wsb
    @3
    @5
    wo
    @2
    @0
    vx
    vy
    wsb
    #
    @5
    wi
    @6
    @0
    wps
    vx
    vy
    sbim
    @8
    @4
    @5
    wph
    vx
    vy
    sbn
    imbi1i
    bitri
    @7
    @1
    vx
    vy
    wph
    wps
    df-or
    sbbii
    @3
    @5
    df-or
    3bitr4i
end
