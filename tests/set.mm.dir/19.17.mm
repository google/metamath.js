include "wb.mm"
include "wal.mm"
include "albi.mm"
include "19.3.mm"
include "syl6bb.mm"

theorem 19.17
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.17.1: |- F/ x ps


  assert |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> ps ) )

  proof
    wph
    wps
    wb
    vx
    wal
    wph
    vx
    wal
    wps
    vx
    wal
    wps
    wph
    wps
    vx
    albi
    wps
    vx
    19.17.1
    19.3
    syl6bb
end
