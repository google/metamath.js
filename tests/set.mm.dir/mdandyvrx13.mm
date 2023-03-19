include "mdandyvrx2.mm"

theorem mdandyvrx13
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
  assume mdandyvrx13.1: |- ( ph \/_ ze )
  assume mdandyvrx13.2: |- ( ps \/_ si )
  assume mdandyvrx13.3: |- ( ch <-> ps )
  assume mdandyvrx13.4: |- ( th <-> ph )
  assume mdandyvrx13.5: |- ( ta <-> ps )
  assume mdandyvrx13.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch \/_ si ) /\ ( th \/_ ze ) ) /\ ( ta \/_ si ) ) /\ ( et \/_ si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvrx13.2
    mdandyvrx13.1
    mdandyvrx13.3
    mdandyvrx13.4
    mdandyvrx13.5
    mdandyvrx13.6
    mdandyvrx2
end
