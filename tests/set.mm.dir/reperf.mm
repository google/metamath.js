include "cr.mm"
include "cv.mm"
include "readdcl.mm"
include "ax-resscn.mm"
include "reperflem.mm"

theorem reperf
  let cJ: class J
  let vn: setvar n
  let vr: setvar r
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cS: class S
  assume recld2.1: |- J = ( TopOpen ` CCfld )


  assert |- ( J |`t RR ) e. Perf

  proof
    vy
    vx
    cr
    cJ
    recld2.1
    vx
    cv
    vy
    cv
    readdcl
    ax-resscn
    reperflem
end
