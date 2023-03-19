include "mdandyvr3.mm"

theorem mdandyvr12
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
  assume mdandyvr12.1: |- ( ph <-> ze )
  assume mdandyvr12.2: |- ( ps <-> si )
  assume mdandyvr12.3: |- ( ch <-> ph )
  assume mdandyvr12.4: |- ( th <-> ph )
  assume mdandyvr12.5: |- ( ta <-> ps )
  assume mdandyvr12.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch <-> ze ) /\ ( th <-> ze ) ) /\ ( ta <-> si ) ) /\ ( et <-> si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvr12.2
    mdandyvr12.1
    mdandyvr12.3
    mdandyvr12.4
    mdandyvr12.5
    mdandyvr12.6
    mdandyvr3
end
