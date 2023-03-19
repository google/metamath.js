include "wn.mm"
include "wl-a1i.mm"
include "wl-syl5.mm"
include "wl-pm2.18d.mm"

theorem wl-mpi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume wl-mpi.1: |- ps
  assume wl-mpi.2: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ch )

  proof
    wph
    wch
    wch
    wn
    #
    wps
    wph
    wch
    wps
    @0
    wl-mpi.1
    wl-a1i
    wl-mpi.2
    wl-syl5
    wl-pm2.18d
end
