include "mdandyvrx6.mm"

theorem mdandyvrx9
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
  assume mdandyvrx9.1: |- ( ph \/_ ze )
  assume mdandyvrx9.2: |- ( ps \/_ si )
  assume mdandyvrx9.3: |- ( ch <-> ps )
  assume mdandyvrx9.4: |- ( th <-> ph )
  assume mdandyvrx9.5: |- ( ta <-> ph )
  assume mdandyvrx9.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch \/_ si ) /\ ( th \/_ ze ) ) /\ ( ta \/_ ze ) ) /\ ( et \/_ si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvrx9.2
    mdandyvrx9.1
    mdandyvrx9.3
    mdandyvrx9.4
    mdandyvrx9.5
    mdandyvrx9.6
    mdandyvrx6
end
