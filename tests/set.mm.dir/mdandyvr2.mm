include "wb.mm"
include "wa.mm"
include "bitri.mm"
include "pm3.2i.mm"

theorem mdandyvr2
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
  assume mdandyvr2.1: |- ( ph <-> ze )
  assume mdandyvr2.2: |- ( ps <-> si )
  assume mdandyvr2.3: |- ( ch <-> ph )
  assume mdandyvr2.4: |- ( th <-> ps )
  assume mdandyvr2.5: |- ( ta <-> ph )
  assume mdandyvr2.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch <-> ze ) /\ ( th <-> si ) ) /\ ( ta <-> ze ) ) /\ ( et <-> ze ) )

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
    wze
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
    mdandyvr2.3
    mdandyvr2.1
    bitri
    wth
    wps
    wsi
    mdandyvr2.4
    mdandyvr2.2
    bitri
    pm3.2i
    wta
    wph
    wze
    mdandyvr2.5
    mdandyvr2.1
    bitri
    pm3.2i
    wet
    wph
    wze
    mdandyvr2.6
    mdandyvr2.1
    bitri
    pm3.2i
end
