include "wn.mm"
include "wal.mm"
include "wi.mm"
include "axc7.mm"
include "con1i.mm"
include "con3.mm"
include "al2imi.mm"
include "syl5.mm"

theorem hbntg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph -> A. x ps ) -> ( -. ps -> A. x -. ph ) )

  proof
    wps
    wn
    wps
    vx
    wal
    #
    wn
    #
    vx
    wal
    #
    wph
    @0
    wi
    #
    vx
    wal
    wph
    wn
    #
    vx
    wal
    @2
    wps
    wps
    vx
    axc7
    con1i
    @3
    @1
    @4
    vx
    wph
    @0
    con3
    al2imi
    syl5
end
