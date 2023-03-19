include "weq.mm"
include "wi.mm"
include "wa.mm"
include "wex.mm"
include "wsb.mm"
include "pm5.4.mm"
include "bicomi.mm"
include "abai.mm"
include "exbii.mm"
include "anbi12i.mm"
include "df-sb.mm"
include "3bitr4i.mm"

theorem sbequ8
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] ph <-> [ y / x ] ( x = y -> ph ) )

  proof
    vx
    vy
    weq
    #
    wph
    wi
    #
    @0
    wph
    wa
    #
    vx
    wex
    #
    wa
    @0
    @1
    wi
    #
    @0
    @1
    wa
    #
    vx
    wex
    #
    wa
    wph
    vx
    vy
    wsb
    @1
    vx
    vy
    wsb
    @1
    @4
    @3
    @6
    @4
    @1
    @0
    wph
    pm5.4
    bicomi
    @2
    @5
    vx
    @0
    wph
    abai
    exbii
    anbi12i
    wph
    vx
    vy
    df-sb
    @1
    vx
    vy
    df-sb
    3bitr4i
end
