include "w3a.mm"
include "wo.mm"
include "or3di.mm"
include "orcom.mm"
include "3anbi123i.mm"
include "3bitr3i.mm"

theorem or3dir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta


  assert |- ( ( ( ph /\ ps /\ ch ) \/ ta ) <-> ( ( ph \/ ta ) /\ ( ps \/ ta ) /\ ( ch \/ ta ) ) )

  proof
    wta
    wph
    wps
    wch
    w3a
    #
    wo
    wta
    wph
    wo
    #
    wta
    wps
    wo
    #
    wta
    wch
    wo
    #
    w3a
    @0
    wta
    wo
    wph
    wta
    wo
    #
    wps
    wta
    wo
    #
    wch
    wta
    wo
    #
    w3a
    wta
    wph
    wps
    wch
    or3di
    wta
    @0
    orcom
    @1
    @4
    @2
    @5
    @3
    @6
    wta
    wph
    orcom
    wta
    wps
    orcom
    wta
    wch
    orcom
    3anbi123i
    3bitr3i
end
