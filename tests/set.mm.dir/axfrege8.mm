include "wi.mm"
include "rp-7frege.mm"
include "rp-8frege.mm"
include "ax-mp.mm"

theorem axfrege8
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wi
    #
    wps
    wph
    wps
    wi
    wph
    wch
    wi
    #
    wi
    wi
    wi
    @0
    wps
    @1
    wi
    wi
    wph
    wps
    wch
    wps
    rp-7frege
    @0
    wps
    wph
    @1
    rp-8frege
    ax-mp
end
