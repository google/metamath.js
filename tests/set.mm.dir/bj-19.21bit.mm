include "wal.mm"
include "sp.mm"
include "imim2i.mm"

theorem bj-19.21bit
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( ph -> A. x ps ) -> ( ph -> ps ) )

  proof
    wps
    vx
    wal
    wps
    wph
    wps
    vx
    sp
    imim2i
end
