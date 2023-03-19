include "wb.mm"
include "wa.mm"
include "bitri.mm"
include "pm3.2i.mm"

theorem mdandyvr3
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
  assume mdandyvr3.1: |- ( ph <-> ze )
  assume mdandyvr3.2: |- ( ps <-> si )
  assume mdandyvr3.3: |- ( ch <-> ps )
  assume mdandyvr3.4: |- ( th <-> ps )
  assume mdandyvr3.5: |- ( ta <-> ph )
  assume mdandyvr3.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch <-> si ) /\ ( th <-> si ) ) /\ ( ta <-> ze ) ) /\ ( et <-> ze ) )

  proof
    wch
    wsi
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
    wps
    wsi
    mdandyvr3.3
    mdandyvr3.2
    bitri
    wth
    wps
    wsi
    mdandyvr3.4
    mdandyvr3.2
    bitri
    pm3.2i
    wta
    wph
    wze
    mdandyvr3.5
    mdandyvr3.1
    bitri
    pm3.2i
    wet
    wph
    wze
    mdandyvr3.6
    mdandyvr3.1
    bitri
    pm3.2i
end
