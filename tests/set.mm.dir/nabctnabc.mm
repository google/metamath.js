include "wn.mm"
include "wa.mm"
include "wb.mm"
include "wi.mm"
include "pm4.61.mm"
include "biimpi.mm"
include "ax-mp.mm"
include "simpli.mm"
include "simpri.mm"
include "2th.mm"
include "bicom.mm"
include "con3i.mm"
include "notnotrd.mm"

theorem nabctnabc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vk: setvar k
  let vx: setvar x
  assume nabctnabc.1: |- -. ( ph -> ( ps /\ ch ) )


  assert |- ( -. ph -> ( ps /\ ch ) )

  proof
    wph
    wn
    wps
    wch
    wa
    #
    @0
    wn
    #
    wph
    @1
    wph
    wph
    @1
    wb
    #
    @1
    wph
    wb
    #
    wph
    @1
    wph
    @1
    wph
    @0
    wi
    wn
    #
    wph
    @1
    wa
    #
    nabctnabc.1
    @4
    @5
    wph
    @0
    pm4.61
    biimpi
    ax-mp
    #
    simpli
    wph
    @1
    @6
    simpri
    2th
    @2
    @3
    wph
    @1
    bicom
    biimpi
    ax-mp
    biimpi
    con3i
    notnotrd
end
