include "mdandyvrx7.mm"

theorem mdandyvrx8
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
  assume mdandyvrx8.1: |- ( ph \/_ ze )
  assume mdandyvrx8.2: |- ( ps \/_ si )
  assume mdandyvrx8.3: |- ( ch <-> ph )
  assume mdandyvrx8.4: |- ( th <-> ph )
  assume mdandyvrx8.5: |- ( ta <-> ph )
  assume mdandyvrx8.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ ze ) ) /\ ( ta \/_ ze ) ) /\ ( et \/_ si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvrx8.2
    mdandyvrx8.1
    mdandyvrx8.3
    mdandyvrx8.4
    mdandyvrx8.5
    mdandyvrx8.6
    mdandyvrx7
end
