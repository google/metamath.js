include "mdandyvrx4.mm"

theorem mdandyvrx11
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
  assume mdandyvrx11.1: |- ( ph \/_ ze )
  assume mdandyvrx11.2: |- ( ps \/_ si )
  assume mdandyvrx11.3: |- ( ch <-> ps )
  assume mdandyvrx11.4: |- ( th <-> ps )
  assume mdandyvrx11.5: |- ( ta <-> ph )
  assume mdandyvrx11.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch \/_ si ) /\ ( th \/_ si ) ) /\ ( ta \/_ ze ) ) /\ ( et \/_ si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvrx11.2
    mdandyvrx11.1
    mdandyvrx11.3
    mdandyvrx11.4
    mdandyvrx11.5
    mdandyvrx11.6
    mdandyvrx4
end
