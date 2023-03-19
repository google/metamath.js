include "wb.mm"
include "wal.mm"
include "sp.mm"
include "albi.mm"
include "imbi12d.mm"

theorem bj-hbxfrbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph <-> ps ) -> ( ( ph -> A. x ph ) <-> ( ps -> A. x ps ) ) )

  proof
    wph
    wps
    wb
    #
    vx
    wal
    wph
    wps
    wph
    vx
    wal
    wps
    vx
    wal
    @0
    vx
    sp
    wph
    wps
    vx
    albi
    imbi12d
end
