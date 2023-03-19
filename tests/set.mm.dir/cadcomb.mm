include "wcad.mm"
include "wo.mm"
include "w3a.mm"
include "cadan.mm"
include "3ancoma.mm"
include "orcom.mm"
include "3anbi3i.mm"
include "3bitri.mm"
include "bitr4i.mm"

theorem cadcomb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( cadd ( ph , ps , ch ) <-> cadd ( ph , ch , ps ) )

  proof
    wph
    wps
    wch
    wcad
    #
    wph
    wch
    wo
    #
    wph
    wps
    wo
    #
    wch
    wps
    wo
    #
    w3a
    #
    wph
    wch
    wps
    wcad
    @0
    @2
    @1
    wps
    wch
    wo
    #
    w3a
    @1
    @2
    @5
    w3a
    @4
    wph
    wps
    wch
    cadan
    @2
    @1
    @5
    3ancoma
    @5
    @3
    @1
    @2
    wps
    wch
    orcom
    3anbi3i
    3bitri
    wph
    wch
    wps
    cadan
    bitr4i
end
