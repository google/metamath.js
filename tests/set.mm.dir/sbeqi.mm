include "wb.mm"
include "wal.mm"
include "wsb.mm"
include "cv.mm"
include "wceq.mm"
include "spsbbi.mm"
include "sbequ.mm"
include "sylan9bbr.mm"

theorem sbeqi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( x = y /\ A. z ( ph <-> ps ) ) -> ( [ x / z ] ph <-> [ y / z ] ps ) )

  proof
    wph
    wps
    wb
    vz
    wal
    wph
    vz
    vx
    wsb
    wps
    vz
    vx
    wsb
    vx
    cv
    vy
    cv
    wceq
    wps
    vz
    vy
    wsb
    wph
    wps
    vz
    vx
    spsbbi
    wps
    vx
    vy
    vz
    sbequ
    sylan9bbr
end
