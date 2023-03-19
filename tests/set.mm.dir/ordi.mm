include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wo.mm"
include "jcab.mm"
include "df-or.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem ordi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ( ps /\ ch ) ) <-> ( ( ph \/ ps ) /\ ( ph \/ ch ) ) )

  proof
    wph
    wn
    #
    wps
    wch
    wa
    #
    wi
    @0
    wps
    wi
    #
    @0
    wch
    wi
    #
    wa
    wph
    @1
    wo
    wph
    wps
    wo
    #
    wph
    wch
    wo
    #
    wa
    @0
    wps
    wch
    jcab
    wph
    @1
    df-or
    @4
    @2
    @5
    @3
    wph
    wps
    df-or
    wph
    wch
    df-or
    anbi12i
    3bitr4i
end
