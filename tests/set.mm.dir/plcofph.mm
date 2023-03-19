include "wa.mm"
include "wb.mm"
include "wn.mm"
include "wi.mm"
include "pm3.24.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "bicomi.mm"
include "biimpi.mm"
include "ax-mp.mm"

theorem plcofph
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vk: setvar k
  let vx: setvar x
  assume plcofph.1: |- ( ch <-> ( ( ( ( ph /\ ps ) <-> ph ) -> ( ph /\ -. ( ph /\ -. ph ) ) ) /\ ( ph /\ -. ( ph /\ -. ph ) ) ) )
  assume plcofph.2: |- ph
  assume plcofph.3: |- ps


  assert |- ch

  proof
    wph
    wps
    wa
    wph
    wb
    #
    wph
    wph
    wph
    wn
    wa
    wn
    #
    wa
    #
    wi
    #
    @2
    wa
    #
    wch
    @3
    @2
    @2
    @0
    wph
    @1
    plcofph.2
    wph
    pm3.24
    pm3.2i
    #
    a1i
    @5
    pm3.2i
    @4
    wch
    wch
    @4
    plcofph.1
    bicomi
    biimpi
    ax-mp
end
