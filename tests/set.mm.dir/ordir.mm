include "wa.mm"
include "wo.mm"
include "ordi.mm"
include "orcom.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem ordir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) \/ ch ) <-> ( ( ph \/ ch ) /\ ( ps \/ ch ) ) )

  proof
    wch
    wph
    wps
    wa
    #
    wo
    wch
    wph
    wo
    #
    wch
    wps
    wo
    #
    wa
    @0
    wch
    wo
    wph
    wch
    wo
    #
    wps
    wch
    wo
    #
    wa
    wch
    wph
    wps
    ordi
    @0
    wch
    orcom
    @3
    @1
    @4
    @2
    wph
    wch
    orcom
    wps
    wch
    orcom
    anbi12i
    3bitr4i
end
