include "wb.mm"
include "wal.mm"
include "albi.mm"
include "alimi.mm"
include "syl.mm"

theorem bj-2albi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ( ph <-> ps ) -> ( A. x A. y ph <-> A. x A. y ps ) )

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
    wal
    #
    wps
    vy
    wal
    #
    wb
    #
    vx
    wal
    @1
    vx
    wal
    @2
    vx
    wal
    wb
    @0
    @3
    vx
    wph
    wps
    vy
    albi
    alimi
    @1
    @2
    vx
    albi
    syl
end
