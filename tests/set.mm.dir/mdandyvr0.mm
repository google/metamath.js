include "wb.mm"
include "wa.mm"
include "bitri.mm"
include "pm3.2i.mm"

theorem mdandyvr0
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
  assume mdandyvr0.1: |- ( ph <-> ze )
  assume mdandyvr0.2: |- ( ps <-> si )
  assume mdandyvr0.3: |- ( ch <-> ph )
  assume mdandyvr0.4: |- ( th <-> ph )
  assume mdandyvr0.5: |- ( ta <-> ph )
  assume mdandyvr0.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch <-> ze ) /\ ( th <-> ze ) ) /\ ( ta <-> ze ) ) /\ ( et <-> ze ) )

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
    mdandyvr0.3
    mdandyvr0.1
    bitri
    wth
    wph
    wze
    mdandyvr0.4
    mdandyvr0.1
    bitri
    pm3.2i
    wta
    wph
    wze
    mdandyvr0.5
    mdandyvr0.1
    bitri
    pm3.2i
    wet
    wph
    wze
    mdandyvr0.6
    mdandyvr0.1
    bitri
    pm3.2i
end
