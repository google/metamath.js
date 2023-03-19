include "wb.mm"
include "wa.mm"
include "bitri.mm"
include "pm3.2i.mm"

theorem mdandyvr5
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
  assume mdandyvr5.1: |- ( ph <-> ze )
  assume mdandyvr5.2: |- ( ps <-> si )
  assume mdandyvr5.3: |- ( ch <-> ps )
  assume mdandyvr5.4: |- ( th <-> ph )
  assume mdandyvr5.5: |- ( ta <-> ps )
  assume mdandyvr5.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch <-> si ) /\ ( th <-> ze ) ) /\ ( ta <-> si ) ) /\ ( et <-> ze ) )

  proof
    wch
    wsi
    wb
    #
    wth
    wze
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
    wps
    wsi
    mdandyvr5.3
    mdandyvr5.2
    bitri
    wth
    wph
    wze
    mdandyvr5.4
    mdandyvr5.1
    bitri
    pm3.2i
    wta
    wps
    wsi
    mdandyvr5.5
    mdandyvr5.2
    bitri
    pm3.2i
    wet
    wph
    wze
    mdandyvr5.6
    mdandyvr5.1
    bitri
    pm3.2i
end
