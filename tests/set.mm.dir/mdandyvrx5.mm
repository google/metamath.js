include "wxo.mm"
include "wa.mm"
include "axorbciffatcxorb.mm"
include "pm3.2i.mm"

theorem mdandyvrx5
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
  assume mdandyvrx5.1: |- ( ph \/_ ze )
  assume mdandyvrx5.2: |- ( ps \/_ si )
  assume mdandyvrx5.3: |- ( ch <-> ps )
  assume mdandyvrx5.4: |- ( th <-> ph )
  assume mdandyvrx5.5: |- ( ta <-> ps )
  assume mdandyvrx5.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch \/_ si ) /\ ( th \/_ ze ) ) /\ ( ta \/_ si ) ) /\ ( et \/_ ze ) )

  proof
    wch
    wsi
    wxo
    #
    wth
    wze
    wxo
    #
    wa
    #
    wta
    wsi
    wxo
    #
    wa
    wet
    wze
    wxo
    @2
    @3
    @0
    @1
    wps
    wsi
    wch
    mdandyvrx5.2
    mdandyvrx5.3
    axorbciffatcxorb
    wph
    wze
    wth
    mdandyvrx5.1
    mdandyvrx5.4
    axorbciffatcxorb
    pm3.2i
    wps
    wsi
    wta
    mdandyvrx5.2
    mdandyvrx5.5
    axorbciffatcxorb
    pm3.2i
    wph
    wze
    wet
    mdandyvrx5.1
    mdandyvrx5.6
    axorbciffatcxorb
    pm3.2i
end
