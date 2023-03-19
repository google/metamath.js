include "wb.mm"
include "wal.mm"
include "wex.mm"
include "exbi.mm"
include "alimi.mm"
include "syl.mm"

theorem 2exbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ( ph <-> ps ) -> ( E. x E. y ph <-> E. x E. y ps ) )

  proof
    wph
    wps
    wb
    vy
    wal
    #
    vx
    wal
    wph
    vy
    wex
    #
    wps
    vy
    wex
    #
    wb
    #
    vx
    wal
    @1
    vx
    wex
    @2
    vx
    wex
    wb
    @0
    @3
    vx
    wph
    wps
    vy
    exbi
    alimi
    @1
    @2
    vx
    exbi
    syl
end
