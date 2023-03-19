include "copab.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "eqopab2b.mm"
include "biimpri.mm"

theorem opabbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x A. y ( ph <-> ps ) -> { <. x , y >. | ph } = { <. x , y >. | ps } )

  proof
    wph
    vx
    vy
    copab
    wps
    vx
    vy
    copab
    wceq
    wph
    wps
    wb
    vy
    wal
    vx
    wal
    wph
    wps
    vx
    vy
    eqopab2b
    biimpri
end
