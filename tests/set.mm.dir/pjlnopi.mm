include "cpjh.mm"
include "cfv.mm"
include "cho.mm"
include "wcel.mm"
include "clo.mm"
include "pjhmopi.mm"
include "hmoplin.mm"
include "ax-mp.mm"

theorem pjlnopi
  let cH: class H
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pjhmop.1: |- H e. CH


  assert |- ( projh ` H ) e. LinOp

  proof
    cH
    cpjh
    cfv
    #
    cho
    wcel
    @0
    clo
    wcel
    cH
    pjhmop.1
    pjhmopi
    @0
    hmoplin
    ax-mp
end
