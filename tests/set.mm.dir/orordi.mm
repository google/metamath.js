include "wo.mm"
include "oridm.mm"
include "orbi1i.mm"
include "or4.mm"
include "bitr3i.mm"

theorem orordi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ( ps \/ ch ) ) <-> ( ( ph \/ ps ) \/ ( ph \/ ch ) ) )

  proof
    wph
    wps
    wch
    wo
    #
    wo
    wph
    wph
    wo
    #
    @0
    wo
    wph
    wps
    wo
    wph
    wch
    wo
    wo
    @1
    wph
    @0
    wph
    oridm
    orbi1i
    wph
    wph
    wps
    wch
    or4
    bitr3i
end
