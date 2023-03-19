include "wi.mm"
include "wo.mm"
include "bi2.04.mm"
include "dfor2.mm"
include "imbi2i.mm"
include "bitr4i.mm"

theorem imimorb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ps -> ch ) -> ( ph -> ch ) ) <-> ( ph -> ( ps \/ ch ) ) )

  proof
    wps
    wch
    wi
    #
    wph
    wch
    wi
    wi
    wph
    @0
    wch
    wi
    #
    wi
    wph
    wps
    wch
    wo
    #
    wi
    @0
    wph
    wch
    bi2.04
    @2
    @1
    wph
    wps
    wch
    dfor2
    imbi2i
    bitr4i
end
