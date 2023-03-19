include "wn.mm"
include "wa.mm"
include "wi.mm"
include "plcofph.mm"
include "pldofph.mm"
include "pm3.2i.mm"
include "pm3.4.mm"
include "ax-mp.mm"
include "iman.mm"
include "biimpi.mm"
include "bicomi.mm"

theorem plvcofphax
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let vk: setvar k
  let vx: setvar x
  assume plvcofphax.1: |- ( ch <-> ( ( ( ( ph /\ ps ) <-> ph ) -> ( ph /\ -. ( ph /\ -. ph ) ) ) /\ ( ph /\ -. ( ph /\ -. ph ) ) ) )
  assume plvcofphax.2: |- ( ta <-> ( ( ch -> th ) /\ ( ph <-> ch ) /\ ( ( ph -> ps ) -> ( ps <-> th ) ) ) )
  assume plvcofphax.3: |- ( et <-> ( ch /\ ta ) )
  assume plvcofphax.4: |- ph
  assume plvcofphax.5: |- ps
  assume plvcofphax.6: |- th
  assume plvcofphax.7: |- ( ze <-> -. ( ps /\ -. ta ) )


  assert |- ze

  proof
    wps
    wta
    wn
    wa
    wn
    #
    wze
    wps
    wta
    wi
    #
    @0
    wps
    wta
    wa
    @1
    wps
    wta
    plvcofphax.5
    wph
    wps
    wch
    wth
    wta
    plvcofphax.2
    plvcofphax.4
    plvcofphax.5
    wph
    wps
    wch
    plvcofphax.1
    plvcofphax.4
    plvcofphax.5
    plcofph
    plvcofphax.6
    pldofph
    pm3.2i
    wps
    wta
    pm3.4
    ax-mp
    @1
    @0
    wps
    wta
    iman
    biimpi
    ax-mp
    @0
    wze
    wze
    @0
    plvcofphax.7
    bicomi
    biimpi
    ax-mp
end
