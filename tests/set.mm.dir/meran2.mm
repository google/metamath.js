include "wn.mm"
include "wo.mm"
include "meran1.mm"
include "imorri.mm"
include "syl.mm"
include "imori.mm"

theorem meran2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( -. ( -. ( -. ph \/ ps ) \/ ( ch \/ ( th \/ ta ) ) ) \/ ( -. ( -. ta \/ th ) \/ ( ch \/ ( ph \/ th ) ) ) )

  proof
    wph
    wn
    wps
    wo
    wn
    wch
    wth
    wta
    wo
    wo
    wo
    #
    wta
    wn
    wth
    wo
    wn
    wch
    wph
    wth
    wo
    wo
    wo
    #
    @0
    wth
    wn
    wph
    wo
    wn
    wch
    wta
    wph
    wo
    wo
    wo
    #
    @1
    @0
    @2
    wph
    wps
    wch
    wth
    wta
    meran1
    imorri
    @2
    @1
    wth
    wph
    wch
    wta
    wph
    meran1
    imorri
    syl
    imori
end
