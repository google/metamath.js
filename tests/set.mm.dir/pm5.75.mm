include "wo.mm"
include "wb.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "anbi1.mm"
include "biorf.mm"
include "bicomd.mm"
include "pm5.32ri.mm"
include "syl6bb.mm"
include "pm4.71.mm"
include "biimpi.mm"
include "sylan9bbr.mm"

theorem pm5.75
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ch -> -. ps ) /\ ( ph <-> ( ps \/ ch ) ) ) -> ( ( ph /\ -. ps ) <-> ch ) )

  proof
    wph
    wps
    wch
    wo
    #
    wb
    #
    wph
    wps
    wn
    #
    wa
    #
    wch
    @2
    wa
    #
    wch
    @2
    wi
    #
    wch
    @1
    @3
    @0
    @2
    wa
    @4
    wph
    @0
    @2
    anbi1
    @2
    @0
    wch
    @2
    wch
    @0
    wps
    wch
    biorf
    bicomd
    pm5.32ri
    syl6bb
    @5
    wch
    @4
    @5
    wch
    @4
    wb
    wch
    @2
    pm4.71
    biimpi
    bicomd
    sylan9bbr
end
