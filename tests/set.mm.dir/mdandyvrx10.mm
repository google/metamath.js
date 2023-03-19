include "mdandyvrx5.mm"

theorem mdandyvrx10
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
  assume mdandyvrx10.1: |- ( ph \/_ ze )
  assume mdandyvrx10.2: |- ( ps \/_ si )
  assume mdandyvrx10.3: |- ( ch <-> ph )
  assume mdandyvrx10.4: |- ( th <-> ps )
  assume mdandyvrx10.5: |- ( ta <-> ph )
  assume mdandyvrx10.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ si ) ) /\ ( ta \/_ ze ) ) /\ ( et \/_ si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvrx10.2
    mdandyvrx10.1
    mdandyvrx10.3
    mdandyvrx10.4
    mdandyvrx10.5
    mdandyvrx10.6
    mdandyvrx5
end
