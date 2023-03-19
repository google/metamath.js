include "wo.mm"
include "wi.mm"
include "wn.mm"
include "imor.mm"
include "orass.mm"
include "bitr4i.mm"

theorem impor
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps \/ ch ) ) <-> ( ( -. ph \/ ps ) \/ ch ) )

  proof
    wph
    wps
    wch
    wo
    #
    wi
    wph
    wn
    #
    @0
    wo
    @1
    wps
    wo
    wch
    wo
    wph
    @0
    imor
    @1
    wps
    wch
    orass
    bitr4i
end
