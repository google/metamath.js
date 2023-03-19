include "wal.mm"
include "wb.mm"
include "19.3.mm"
include "albi.mm"
include "syl5bbr.mm"

theorem 19.16
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.16.1: |- F/ x ph


  assert |- ( A. x ( ph <-> ps ) -> ( ph <-> A. x ps ) )

  proof
    wph
    wph
    vx
    wal
    wph
    wps
    wb
    vx
    wal
    wps
    vx
    wal
    wph
    vx
    19.16.1
    19.3
    wph
    wps
    vx
    albi
    syl5bbr
end
