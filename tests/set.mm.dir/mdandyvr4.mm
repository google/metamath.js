include "wb.mm"
include "wa.mm"
include "bitri.mm"
include "pm3.2i.mm"

theorem mdandyvr4
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
  assume mdandyvr4.1: |- ( ph <-> ze )
  assume mdandyvr4.2: |- ( ps <-> si )
  assume mdandyvr4.3: |- ( ch <-> ph )
  assume mdandyvr4.4: |- ( th <-> ph )
  assume mdandyvr4.5: |- ( ta <-> ps )
  assume mdandyvr4.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch <-> ze ) /\ ( th <-> ze ) ) /\ ( ta <-> si ) ) /\ ( et <-> ze ) )

  proof
    wch
    wze
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
    wph
    wze
    mdandyvr4.3
    mdandyvr4.1
    bitri
    wth
    wph
    wze
    mdandyvr4.4
    mdandyvr4.1
    bitri
    pm3.2i
    wta
    wps
    wsi
    mdandyvr4.5
    mdandyvr4.2
    bitri
    pm3.2i
    wet
    wph
    wze
    mdandyvr4.6
    mdandyvr4.1
    bitri
    pm3.2i
end
