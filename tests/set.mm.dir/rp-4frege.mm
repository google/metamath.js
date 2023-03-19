include "wi.mm"
include "rp-simp2-frege.mm"
include "rp-misc1-frege.mm"
include "ax-mp.mm"

theorem rp-4frege
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ( ps -> ph ) -> ch ) ) -> ( ph -> ch ) )

  proof
    wph
    wps
    wph
    wi
    #
    wch
    wi
    wi
    #
    wph
    @0
    wi
    wi
    @1
    wph
    wch
    wi
    wi
    @1
    wph
    wps
    rp-simp2-frege
    wph
    @0
    wch
    rp-misc1-frege
    ax-mp
end
