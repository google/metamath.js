include "mdandyvrx0.mm"

theorem mdandyvrx15
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
  assume mdandyvrx15.1: |- ( ph \/_ ze )
  assume mdandyvrx15.2: |- ( ps \/_ si )
  assume mdandyvrx15.3: |- ( ch <-> ps )
  assume mdandyvrx15.4: |- ( th <-> ps )
  assume mdandyvrx15.5: |- ( ta <-> ps )
  assume mdandyvrx15.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch \/_ si ) /\ ( th \/_ si ) ) /\ ( ta \/_ si ) ) /\ ( et \/_ si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvrx15.2
    mdandyvrx15.1
    mdandyvrx15.3
    mdandyvrx15.4
    mdandyvrx15.5
    mdandyvrx15.6
    mdandyvrx0
end
