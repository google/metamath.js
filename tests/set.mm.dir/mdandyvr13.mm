include "mdandyvr2.mm"

theorem mdandyvr13
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
  assume mdandyvr13.1: |- ( ph <-> ze )
  assume mdandyvr13.2: |- ( ps <-> si )
  assume mdandyvr13.3: |- ( ch <-> ps )
  assume mdandyvr13.4: |- ( th <-> ph )
  assume mdandyvr13.5: |- ( ta <-> ps )
  assume mdandyvr13.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch <-> si ) /\ ( th <-> ze ) ) /\ ( ta <-> si ) ) /\ ( et <-> si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvr13.2
    mdandyvr13.1
    mdandyvr13.3
    mdandyvr13.4
    mdandyvr13.5
    mdandyvr13.6
    mdandyvr2
end
