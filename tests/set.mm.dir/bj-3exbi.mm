include "wb.mm"
include "wal.mm"
include "wex.mm"
include "exbi.mm"
include "2alimi.mm"
include "bj-2exbi.mm"
include "syl.mm"

theorem bj-3exbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x A. y A. z ( ph <-> ps ) -> ( E. x E. y E. z ph <-> E. x E. y E. z ps ) )

  proof
    wph
    wps
    wb
    vz
    wal
    #
    vy
    wal
    vx
    wal
    wph
    vz
    wex
    #
    wps
    vz
    wex
    #
    wb
    #
    vy
    wal
    vx
    wal
    @1
    vy
    wex
    vx
    wex
    @2
    vy
    wex
    vx
    wex
    wb
    @0
    @3
    vx
    vy
    wph
    wps
    vz
    exbi
    2alimi
    @1
    @2
    vx
    vy
    bj-2exbi
    syl
end
