include "wb.mm"
include "wa.mm"
include "bitri.mm"
include "pm3.2i.mm"

theorem mdandyvr1
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
  assume mdandyvr1.1: |- ( ph <-> ze )
  assume mdandyvr1.2: |- ( ps <-> si )
  assume mdandyvr1.3: |- ( ch <-> ps )
  assume mdandyvr1.4: |- ( th <-> ph )
  assume mdandyvr1.5: |- ( ta <-> ph )
  assume mdandyvr1.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch <-> si ) /\ ( th <-> ze ) ) /\ ( ta <-> ze ) ) /\ ( et <-> ze ) )

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
    mdandyvr1.3
    mdandyvr1.2
    bitri
    wth
    wph
    wze
    mdandyvr1.4
    mdandyvr1.1
    bitri
    pm3.2i
    wta
    wph
    wze
    mdandyvr1.5
    mdandyvr1.1
    bitri
    pm3.2i
    wet
    wph
    wze
    mdandyvr1.6
    mdandyvr1.1
    bitri
    pm3.2i
end
