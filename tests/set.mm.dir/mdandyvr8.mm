include "mdandyvr7.mm"

theorem mdandyvr8
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
  assume mdandyvr8.1: |- ( ph <-> ze )
  assume mdandyvr8.2: |- ( ps <-> si )
  assume mdandyvr8.3: |- ( ch <-> ph )
  assume mdandyvr8.4: |- ( th <-> ph )
  assume mdandyvr8.5: |- ( ta <-> ph )
  assume mdandyvr8.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch <-> ze ) /\ ( th <-> ze ) ) /\ ( ta <-> ze ) ) /\ ( et <-> si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvr8.2
    mdandyvr8.1
    mdandyvr8.3
    mdandyvr8.4
    mdandyvr8.5
    mdandyvr8.6
    mdandyvr7
end
