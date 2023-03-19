include "cio.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "cab.mm"
include "cuni.mm"
include "dfiota2.mm"
include "nfaba1.mm"
include "nfuni.mm"
include "nfcxfr.mm"

theorem nfiota1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- F/_ x ( iota x ph )

  proof
    vx
    wph
    vx
    cio
    wph
    vx
    vy
    weq
    wb
    #
    vx
    wal
    vy
    cab
    #
    cuni
    wph
    vx
    vy
    dfiota2
    vx
    @1
    @0
    vx
    vy
    nfaba1
    nfuni
    nfcxfr
end
