include "wn.mm"
include "wo.mm"
include "wi.mm"
include "pm2.3.mm"
include "imim2i.mm"
include "pm1.5.mm"
include "syl6.mm"
include "imor.mm"
include "3imtr3i.mm"
include "meran1.mm"
include "imorri.mm"
include "syl.mm"
include "imori.mm"

theorem meran3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( -. ( -. ( -. ph \/ ps ) \/ ( ch \/ ( th \/ ta ) ) ) \/ ( -. ( -. ch \/ ph ) \/ ( ta \/ ( th \/ ph ) ) ) )

  proof
    wph
    wn
    wps
    wo
    #
    wn
    #
    wch
    wth
    wta
    wo
    wo
    #
    wo
    #
    wch
    wn
    wph
    wo
    wn
    wta
    wth
    wph
    wo
    wo
    wo
    #
    @3
    @1
    wta
    wch
    wth
    wo
    wo
    #
    wo
    #
    @4
    @0
    @2
    wi
    #
    @0
    @5
    wi
    @3
    @6
    @7
    @0
    wch
    wta
    wth
    wo
    wo
    #
    @5
    @2
    @8
    @0
    wch
    wth
    wta
    pm2.3
    imim2i
    wch
    wta
    wth
    pm1.5
    syl6
    @0
    @2
    imor
    @0
    @5
    imor
    3imtr3i
    @6
    @4
    wph
    wps
    wta
    wch
    wth
    meran1
    imorri
    syl
    imori
end
