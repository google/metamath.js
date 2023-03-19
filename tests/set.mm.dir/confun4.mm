include "wi.mm"
include "wa.mm"
include "ax-mp.mm"
include "wb.mm"
include "bicom1.mm"
include "biimpi.mm"
include "pm3.2i.mm"
include "pm3.4.mm"

theorem confun4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume confun4.1: |- ph
  assume confun4.2: |- ( ( ph -> ps ) -> ps )
  assume confun4.3: |- ( ps -> ( ph -> ch ) )
  assume confun4.4: |- ( ( ch -> th ) -> ( ( ph -> th ) <-> ps ) )
  assume confun4.5: |- ( ta <-> ( ch -> th ) )
  assume confun4.6: |- ( et <-> -. ( ch -> ( ch /\ -. ch ) ) )
  assume confun4.7: |- ps
  assume confun4.8: |- ( ch -> th )


  assert |- ( ch -> ( ps -> ta ) )

  proof
    wch
    wps
    wta
    wi
    #
    wa
    wch
    @0
    wi
    wch
    @0
    wph
    wch
    confun4.1
    wps
    wph
    wch
    wi
    confun4.7
    confun4.3
    ax-mp
    ax-mp
    wps
    wta
    wa
    @0
    wps
    wta
    confun4.7
    wch
    wth
    wi
    #
    wta
    confun4.8
    @1
    wta
    wta
    @1
    wb
    @1
    wta
    wb
    confun4.5
    wta
    @1
    bicom1
    ax-mp
    biimpi
    ax-mp
    pm3.2i
    wps
    wta
    pm3.4
    ax-mp
    pm3.2i
    wch
    @0
    pm3.4
    ax-mp
end
