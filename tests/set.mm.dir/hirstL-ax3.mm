include "wn.mm"
include "wi.mm"
include "wo.mm"
include "pm4.64.mm"
include "pm4.66.mm"
include "pm2.64.mm"
include "com12.mm"
include "sylbi.mm"
include "syl5bi.mm"

theorem hirstL-ax3
  let wph: wff ph
  let wps: wff ps
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( -. ph -> -. ps ) -> ( ( -. ph -> ps ) -> ph ) )

  proof
    wph
    wn
    #
    wps
    wi
    wph
    wps
    wo
    #
    @0
    wps
    wn
    #
    wi
    #
    wph
    wph
    wps
    pm4.64
    @3
    wph
    @2
    wo
    #
    @1
    wph
    wi
    wph
    wps
    pm4.66
    @1
    @4
    wph
    wph
    wps
    pm2.64
    com12
    sylbi
    syl5bi
end
