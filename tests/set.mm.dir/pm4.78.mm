include "wn.mm"
include "wo.mm"
include "wi.mm"
include "orordi.mm"
include "imor.mm"
include "orbi12i.mm"
include "3bitr4ri.mm"

theorem pm4.78
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) \/ ( ph -> ch ) ) <-> ( ph -> ( ps \/ ch ) ) )

  proof
    wph
    wn
    #
    wps
    wch
    wo
    #
    wo
    @0
    wps
    wo
    #
    @0
    wch
    wo
    #
    wo
    wph
    @1
    wi
    wph
    wps
    wi
    #
    wph
    wch
    wi
    #
    wo
    @0
    wps
    wch
    orordi
    wph
    @1
    imor
    @4
    @2
    @5
    @3
    wph
    wps
    imor
    wph
    wch
    imor
    orbi12i
    3bitr4ri
end
