include "wb.mm"
include "wa.mm"
include "bitri.mm"
include "pm3.2i.mm"

theorem mdandyvr6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let vk: setvar k
  let vx: setvar x
  assume mdandyvr6.1: |- ( ph <-> ze )
  assume mdandyvr6.2: |- ( ps <-> si )
  assume mdandyvr6.3: |- ( ch <-> ph )
  assume mdandyvr6.4: |- ( th <-> ps )
  assume mdandyvr6.5: |- ( ta <-> ps )
  assume mdandyvr6.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch <-> ze ) /\ ( th <-> si ) ) /\ ( ta <-> si ) ) /\ ( et <-> ze ) )

  proof
    wch
    wze
    wb
    #
    wth
    wsi
    wb
    #
    wa
    #
    wta
    wsi
    wb
    #
    wa
    wet
    wze
    wb
    @2
    @3
    @0
    @1
    wch
    wph
    wze
    mdandyvr6.3
    mdandyvr6.1
    bitri
    wth
    wps
    wsi
    mdandyvr6.4
    mdandyvr6.2
    bitri
    pm3.2i
    wta
    wps
    wsi
    mdandyvr6.5
    mdandyvr6.2
    bitri
    pm3.2i
    wet
    wph
    wze
    mdandyvr6.6
    mdandyvr6.1
    bitri
    pm3.2i
end
