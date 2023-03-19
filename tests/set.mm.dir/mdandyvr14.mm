include "mdandyvr1.mm"

theorem mdandyvr14
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
  assume mdandyvr14.1: |- ( ph <-> ze )
  assume mdandyvr14.2: |- ( ps <-> si )
  assume mdandyvr14.3: |- ( ch <-> ph )
  assume mdandyvr14.4: |- ( th <-> ps )
  assume mdandyvr14.5: |- ( ta <-> ps )
  assume mdandyvr14.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch <-> ze ) /\ ( th <-> si ) ) /\ ( ta <-> si ) ) /\ ( et <-> si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvr14.2
    mdandyvr14.1
    mdandyvr14.3
    mdandyvr14.4
    mdandyvr14.5
    mdandyvr14.6
    mdandyvr1
end
