include "wxo.mm"
include "wa.mm"
include "axorbciffatcxorb.mm"
include "pm3.2i.mm"

theorem mdandyvrx4
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
  assume mdandyvrx4.1: |- ( ph \/_ ze )
  assume mdandyvrx4.2: |- ( ps \/_ si )
  assume mdandyvrx4.3: |- ( ch <-> ph )
  assume mdandyvrx4.4: |- ( th <-> ph )
  assume mdandyvrx4.5: |- ( ta <-> ps )
  assume mdandyvrx4.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ ze ) ) /\ ( ta \/_ si ) ) /\ ( et \/_ ze ) )

  proof
    wch
    wze
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
    wph
    wze
    wch
    mdandyvrx4.1
    mdandyvrx4.3
    axorbciffatcxorb
    wph
    wze
    wth
    mdandyvrx4.1
    mdandyvrx4.4
    axorbciffatcxorb
    pm3.2i
    wps
    wsi
    wta
    mdandyvrx4.2
    mdandyvrx4.5
    axorbciffatcxorb
    pm3.2i
    wph
    wze
    wet
    mdandyvrx4.1
    mdandyvrx4.6
    axorbciffatcxorb
    pm3.2i
end
