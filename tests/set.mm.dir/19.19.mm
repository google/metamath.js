include "wex.mm"
include "wb.mm"
include "wal.mm"
include "19.9.mm"
include "exbi.mm"
include "syl5bbr.mm"

theorem 19.19
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume 19.19.1: |- F/ x ph


  assert |- ( A. x ( ph <-> ps ) -> ( ph <-> E. x ps ) )

  proof
    wph
    wph
    vx
    wex
    wph
    wps
    wb
    vx
    wal
    wps
    vx
    wex
    wph
    vx
    19.19.1
    19.9
    wph
    wps
    vx
    exbi
    syl5bbr
end
