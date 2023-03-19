include "wb.mm"
include "wal.mm"
include "wsb.mm"
include "stdpc4.mm"
include "sbbi.mm"
include "sylib.mm"

theorem spsbbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ( ph <-> ps ) -> ( [ y / x ] ph <-> [ y / x ] ps ) )

  proof
    wph
    wps
    wb
    #
    vx
    wal
    @0
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    wps
    vx
    vy
    wsb
    wb
    @0
    vx
    vy
    stdpc4
    wph
    wps
    vx
    vy
    sbbi
    sylib
end
