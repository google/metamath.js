include "mdandyvr6.mm"

theorem mdandyvr9
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
  assume mdandyvr9.1: |- ( ph <-> ze )
  assume mdandyvr9.2: |- ( ps <-> si )
  assume mdandyvr9.3: |- ( ch <-> ps )
  assume mdandyvr9.4: |- ( th <-> ph )
  assume mdandyvr9.5: |- ( ta <-> ph )
  assume mdandyvr9.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch <-> si ) /\ ( th <-> ze ) ) /\ ( ta <-> ze ) ) /\ ( et <-> si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvr9.2
    mdandyvr9.1
    mdandyvr9.3
    mdandyvr9.4
    mdandyvr9.5
    mdandyvr9.6
    mdandyvr6
end
