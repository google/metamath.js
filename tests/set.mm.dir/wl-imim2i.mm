include "wi.mm"
include "ax-luk1.mm"
include "wl-mpi.mm"

theorem wl-imim2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume wl-imim2i.1: |- ( ph -> ps )


  assert |- ( ( ch -> ph ) -> ( ch -> ps ) )

  proof
    wch
    wph
    wi
    wph
    wps
    wi
    wch
    wps
    wi
    wl-imim2i.1
    wch
    wph
    wps
    ax-luk1
    wl-mpi
end
