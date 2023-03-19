include "mdandyvrx3.mm"

theorem mdandyvrx12
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
  assume mdandyvrx12.1: |- ( ph \/_ ze )
  assume mdandyvrx12.2: |- ( ps \/_ si )
  assume mdandyvrx12.3: |- ( ch <-> ph )
  assume mdandyvrx12.4: |- ( th <-> ph )
  assume mdandyvrx12.5: |- ( ta <-> ps )
  assume mdandyvrx12.6: |- ( et <-> ps )


  assert |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ ze ) ) /\ ( ta \/_ si ) ) /\ ( et \/_ si ) )

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wsi
    wze
    mdandyvrx12.2
    mdandyvrx12.1
    mdandyvrx12.3
    mdandyvrx12.4
    mdandyvrx12.5
    mdandyvrx12.6
    mdandyvrx3
end
