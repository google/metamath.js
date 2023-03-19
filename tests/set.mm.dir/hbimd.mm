include "wi.mm"
include "nf5dh.mm"
include "nfimd.mm"
include "nf5rd.mm"

theorem hbimd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume hbimd.1: |- ( ph -> A. x ph )
  assume hbimd.2: |- ( ph -> ( ps -> A. x ps ) )
  assume hbimd.3: |- ( ph -> ( ch -> A. x ch ) )


  assert |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    vx
    wph
    wps
    wch
    vx
    wph
    wps
    vx
    hbimd.1
    hbimd.2
    nf5dh
    wph
    wch
    vx
    hbimd.1
    hbimd.3
    nf5dh
    nfimd
    nf5rd
end
