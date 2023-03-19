include "wi.mm"
include "ax-frege1.mm"
include "ax-mp.mm"

theorem rp-simp2-frege
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ph -> ( ps -> ( ch -> ps ) ) )

  proof
    wps
    wch
    wps
    wi
    wi
    #
    wph
    @0
    wi
    wps
    wch
    ax-frege1
    @0
    wph
    ax-frege1
    ax-mp
end
