include "wb.mm"
include "wo.mm"
include "orbidi.mm"
include "orcom.mm"
include "bibi12i.mm"
include "bitr2i.mm"

theorem pm5.7
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph \/ ch ) <-> ( ps \/ ch ) ) <-> ( ch \/ ( ph <-> ps ) ) )

  proof
    wch
    wph
    wps
    wb
    wo
    wch
    wph
    wo
    #
    wch
    wps
    wo
    #
    wb
    wph
    wch
    wo
    #
    wps
    wch
    wo
    #
    wb
    wch
    wph
    wps
    orbidi
    @0
    @2
    @1
    @3
    wch
    wph
    orcom
    wch
    wps
    orcom
    bibi12i
    bitr2i
end
