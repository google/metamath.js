include "wb.mm"
include "wa.mm"
include "bitri.mm"
include "pm3.2i.mm"

theorem mdandyvr7
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
  assume mdandyvr7.1: |- ( ph <-> ze )
  assume mdandyvr7.2: |- ( ps <-> si )
  assume mdandyvr7.3: |- ( ch <-> ps )
  assume mdandyvr7.4: |- ( th <-> ps )
  assume mdandyvr7.5: |- ( ta <-> ps )
  assume mdandyvr7.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch <-> si ) /\ ( th <-> si ) ) /\ ( ta <-> si ) ) /\ ( et <-> ze ) )

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
    mdandyvr7.3
    mdandyvr7.2
    bitri
    wth
    wps
    wsi
    mdandyvr7.4
    mdandyvr7.2
    bitri
    pm3.2i
    wta
    wps
    wsi
    mdandyvr7.5
    mdandyvr7.2
    bitri
    pm3.2i
    wet
    wph
    wze
    mdandyvr7.6
    mdandyvr7.1
    bitri
    pm3.2i
end
