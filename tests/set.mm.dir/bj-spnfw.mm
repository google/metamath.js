include "wal.mm"
include "wex.mm"
include "19.2.mm"
include "imim1i.mm"

theorem bj-spnfw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( E. x ph -> ps ) -> ( A. x ph -> ps ) )

  proof
    wph
    vx
    wal
    wph
    vx
    wex
    wps
    wph
    vx
    19.2
    imim1i
end
