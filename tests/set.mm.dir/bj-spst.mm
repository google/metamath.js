include "wal.mm"
include "sp.mm"
include "imim1i.mm"

theorem bj-spst
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( ph -> ps ) -> ( A. x ph -> ps ) )

  proof
    wph
    vx
    wal
    wph
    wps
    wph
    vx
    sp
    imim1i
end
