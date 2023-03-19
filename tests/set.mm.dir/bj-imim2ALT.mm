include "wi.mm"
include "ax-1.mm"
include "a2d.mm"

theorem bj-imim2ALT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) )

  proof
    wph
    wps
    wi
    #
    wch
    wph
    wps
    @0
    wch
    ax-1
    a2d
end
