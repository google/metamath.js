include "wi.mm"
include "wal.mm"
include "alim.mm"
include "imim2d.mm"

theorem sylgt
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( A. x ( ps -> ch ) -> ( ( ph -> A. x ps ) -> ( ph -> A. x ch ) ) )

  proof
    wps
    wch
    wi
    vx
    wal
    wps
    vx
    wal
    wch
    vx
    wal
    wph
    wps
    wch
    vx
    alim
    imim2d
end
