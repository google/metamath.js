include "wxo.mm"
include "wa.mm"
include "axorbciffatcxorb.mm"
include "pm3.2i.mm"

theorem mdandyvrx2
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
  assume mdandyvrx2.1: |- ( ph \/_ ze )
  assume mdandyvrx2.2: |- ( ps \/_ si )
  assume mdandyvrx2.3: |- ( ch <-> ph )
  assume mdandyvrx2.4: |- ( th <-> ps )
  assume mdandyvrx2.5: |- ( ta <-> ph )
  assume mdandyvrx2.6: |- ( et <-> ph )


  assert |- ( ( ( ( ch \/_ ze ) /\ ( th \/_ si ) ) /\ ( ta \/_ ze ) ) /\ ( et \/_ ze ) )

  proof
    wch
    wze
    wxo
    #
    wth
    wsi
    wxo
    #
    wa
    #
    wta
    wze
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
    mdandyvrx2.1
    mdandyvrx2.3
    axorbciffatcxorb
    wps
    wsi
    wth
    mdandyvrx2.2
    mdandyvrx2.4
    axorbciffatcxorb
    pm3.2i
    wph
    wze
    wta
    mdandyvrx2.1
    mdandyvrx2.5
    axorbciffatcxorb
    pm3.2i
    wph
    wze
    wet
    mdandyvrx2.1
    mdandyvrx2.6
    axorbciffatcxorb
    pm3.2i
end
