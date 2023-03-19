include "wa.mm"
include "plcofph.mm"
include "pldofph.mm"
include "pm3.2i.mm"
include "bicomi.mm"
include "biimpi.mm"
include "ax-mp.mm"

theorem plvcofph
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume plvcofph.1: |- ( ch <-> ( ( ( ( ph /\ ps ) <-> ph ) -> ( ph /\ -. ( ph /\ -. ph ) ) ) /\ ( ph /\ -. ( ph /\ -. ph ) ) ) )
  assume plvcofph.2: |- ( ta <-> ( ( ch -> th ) /\ ( ph <-> ch ) /\ ( ( ph -> ps ) -> ( ps <-> th ) ) ) )
  assume plvcofph.3: |- ( et <-> ( ch /\ ta ) )
  assume plvcofph.4: |- ph
  assume plvcofph.5: |- ps
  assume plvcofph.6: |- th


  assert |- et

  proof
    wch
    wta
    wa
    #
    wet
    wch
    wta
    wph
    wps
    wch
    plvcofph.1
    plvcofph.4
    plvcofph.5
    plcofph
    #
    wph
    wps
    wch
    wth
    wta
    plvcofph.2
    plvcofph.4
    plvcofph.5
    @1
    plvcofph.6
    pldofph
    pm3.2i
    @0
    wet
    wet
    @0
    plvcofph.3
    bicomi
    biimpi
    ax-mp
end
