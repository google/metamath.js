include "mdandyvrx1.mm"

theorem mdandyvrx14
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
  assume mdandyvrx14.1: |- ( ph \/_ ze )
  assume mdandyvrx14.2: |- ( ps \/_ si )
  assume mdandyvrx14.3: |- ( ch <-> ph )
  assume mdandyvrx14.4: |- ( th <-> ps )
  assume mdandyvrx14.5: |- ( ta <-> ps )
  assume mdandyvrx14.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ si ) ) /\ ( ta \/_ si ) ) /\ ( et \/_ si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvrx14.2
    mdandyvrx14.1
    mdandyvrx14.3
    mdandyvrx14.4
    mdandyvrx14.5
    mdandyvrx14.6
    mdandyvrx1
end
