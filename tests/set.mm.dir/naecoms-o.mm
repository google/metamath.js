include "weq.mm"
include "wal.mm"
include "aecom-o.mm"
include "nsyl4.mm"
include "con1i.mm"

theorem naecoms-o
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume nalequcoms-o.1: |- ( -. A. x x = y -> ph )


  assert |- ( -. A. y y = x -> ph )

  proof
    wph
    vy
    vx
    weq
    vy
    wal
    #
    vx
    vy
    weq
    vx
    wal
    @0
    wph
    vx
    vy
    aecom-o
    nalequcoms-o.1
    nsyl4
    con1i
end
