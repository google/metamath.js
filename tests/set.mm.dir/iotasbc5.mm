include "cio.mm"
include "wsbc.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "weu.mm"
include "sbc5.mm"
include "a1i.mm"

theorem iotasbc5
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  disjoint ph y
  assert |- ( E! x ph -> ( [. ( iota x ph ) / y ]. ps <-> E. y ( y = ( iota x ph ) /\ ps ) ) )

  proof
    wps
    vy
    wph
    vx
    cio
    #
    wsbc
    vy
    cv
    @0
    wceq
    wps
    wa
    vy
    wex
    wb
    wph
    vx
    weu
    wps
    vy
    @0
    sbc5
    a1i
end
