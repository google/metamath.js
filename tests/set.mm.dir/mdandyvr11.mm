include "mdandyvr4.mm"

theorem mdandyvr11
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
  assume mdandyvr11.1: |- ( ph <-> ze )
  assume mdandyvr11.2: |- ( ps <-> si )
  assume mdandyvr11.3: |- ( ch <-> ps )
  assume mdandyvr11.4: |- ( th <-> ps )
  assume mdandyvr11.5: |- ( ta <-> ph )
  assume mdandyvr11.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch <-> si ) /\ ( th <-> si ) ) /\ ( ta <-> ze ) ) /\ ( et <-> si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvr11.2
    mdandyvr11.1
    mdandyvr11.3
    mdandyvr11.4
    mdandyvr11.5
    mdandyvr11.6
    mdandyvr4
end
