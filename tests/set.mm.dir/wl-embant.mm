include "wi.mm"
include "imim2i.mm"
include "mpi.mm"

theorem wl-embant
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume wl-embant.1: |- ph
  assume wl-embant.2: |- ( ps -> ch )


  assert |- ( ( ph -> ps ) -> ch )

  proof
    wph
    wps
    wi
    wph
    wch
    wl-embant.1
    wps
    wch
    wph
    wl-embant.2
    imim2i
    mpi
end
