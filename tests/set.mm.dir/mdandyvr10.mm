include "mdandyvr5.mm"

theorem mdandyvr10
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
  assume mdandyvr10.1: |- ( ph <-> ze )
  assume mdandyvr10.2: |- ( ps <-> si )
  assume mdandyvr10.3: |- ( ch <-> ph )
  assume mdandyvr10.4: |- ( th <-> ps )
  assume mdandyvr10.5: |- ( ta <-> ph )
  assume mdandyvr10.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch <-> ze ) /\ ( th <-> si ) ) /\ ( ta <-> ze ) ) /\ ( et <-> si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvr10.2
    mdandyvr10.1
    mdandyvr10.3
    mdandyvr10.4
    mdandyvr10.5
    mdandyvr10.6
    mdandyvr5
end
