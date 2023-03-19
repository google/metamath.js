include "weq.mm"
include "wsb.mm"
include "cv.mm"
include "wsbc.mm"
include "wb.mm"
include "eqid.mm"
include "dfsbcq2.mm"
include "ax-mp.mm"

theorem sbsbc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] ph <-> [. y / x ]. ph )

  proof
    vy
    vy
    weq
    wph
    vx
    vy
    wsb
    wph
    vx
    vy
    cv
    #
    wsbc
    wb
    @0
    eqid
    wph
    vx
    vy
    @0
    dfsbcq2
    ax-mp
end
