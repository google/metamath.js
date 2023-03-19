include "mdandyvr0.mm"

theorem mdandyvr15
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
  assume mdandyvr15.1: |- ( ph <-> ze )
  assume mdandyvr15.2: |- ( ps <-> si )
  assume mdandyvr15.3: |- ( ch <-> ps )
  assume mdandyvr15.4: |- ( th <-> ps )
  assume mdandyvr15.5: |- ( ta <-> ps )
  assume mdandyvr15.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch <-> si ) /\ ( th <-> si ) ) /\ ( ta <-> si ) ) /\ ( et <-> si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvr15.2
    mdandyvr15.1
    mdandyvr15.3
    mdandyvr15.4
    mdandyvr15.5
    mdandyvr15.6
    mdandyvr0
end
