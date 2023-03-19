include "wi.mm"
include "rp-simp2-frege.mm"
include "ax-frege2.mm"
include "ax-mp.mm"

theorem rp-frege24
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) )

  proof
    wph
    wps
    wch
    wps
    wi
    #
    wi
    wi
    wph
    wps
    wi
    wph
    @0
    wi
    wi
    wph
    wps
    wch
    rp-simp2-frege
    wph
    wps
    @0
    ax-frege2
    ax-mp
end
