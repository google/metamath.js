include "wi.mm"
include "wb.mm"
include "w3a.mm"
include "a1i.mm"
include "2th.mm"
include "3pm3.2i.mm"
include "bicomi.mm"
include "biimpi.mm"
include "ax-mp.mm"

theorem pldofph
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vk: setvar k
  let vx: setvar x
  assume pldofph.1: |- ( ta <-> ( ( ch -> th ) /\ ( ph <-> ch ) /\ ( ( ph -> ps ) -> ( ps <-> th ) ) ) )
  assume pldofph.2: |- ph
  assume pldofph.3: |- ps
  assume pldofph.4: |- ch
  assume pldofph.5: |- th


  assert |- ta

  proof
    wch
    wth
    wi
    #
    wph
    wch
    wb
    #
    wph
    wps
    wi
    #
    wps
    wth
    wb
    #
    wi
    #
    w3a
    #
    wta
    @0
    @1
    @4
    wth
    wch
    pldofph.5
    a1i
    wph
    wch
    pldofph.2
    pldofph.4
    2th
    @3
    @2
    wps
    wth
    pldofph.3
    pldofph.5
    2th
    a1i
    3pm3.2i
    @5
    wta
    wta
    @5
    pldofph.1
    bicomi
    biimpi
    ax-mp
end
