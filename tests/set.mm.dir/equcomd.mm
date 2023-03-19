include "weq.mm"
include "equcom.mm"
include "sylib.mm"

theorem equcomd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume equcomd.1: |- ( ph -> x = y )


  assert |- ( ph -> y = x )

  proof
    wph
    vx
    vy
    weq
    vy
    vx
    weq
    equcomd.1
    vx
    vy
    equcom
    sylib
end
