include "coprab.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "eqoprab2b.mm"
include "biimpri.mm"

theorem oprabbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x A. y A. z ( ph <-> ps ) -> { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , z >. | ps } )

  proof
    wph
    vx
    vy
    vz
    coprab
    wps
    vx
    vy
    vz
    coprab
    wceq
    wph
    wps
    wb
    vz
    wal
    vy
    wal
    vx
    wal
    wph
    wps
    vx
    vy
    vz
    eqoprab2b
    biimpri
end
