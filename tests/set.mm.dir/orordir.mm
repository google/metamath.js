include "wo.mm"
include "oridm.mm"
include "orbi2i.mm"
include "or4.mm"
include "bitr3i.mm"

theorem orordir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ( ps \/ ch ) ) )

  proof
    wph
    wps
    wo
    #
    wch
    wo
    @0
    wch
    wch
    wo
    #
    wo
    wph
    wch
    wo
    wps
    wch
    wo
    wo
    @1
    wch
    @0
    wch
    oridm
    orbi2i
    wph
    wps
    wch
    wch
    or4
    bitr3i
end
