include "wi.mm"
include "ax-1.mm"
include "imim1i.mm"

theorem jarr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) )

  proof
    wps
    wph
    wps
    wi
    wch
    wps
    wph
    ax-1
    imim1i
end
