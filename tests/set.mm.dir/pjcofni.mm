include "cpjh.mm"
include "cfv.mm"
include "pjfi.mm"
include "hocofni.mm"

theorem pjcofni
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( ( projh ` G ) o. ( projh ` H ) ) Fn ~H

  proof
    cG
    cpjh
    cfv
    cH
    cpjh
    cfv
    cG
    pjco.1
    pjfi
    cH
    pjco.2
    pjfi
    hocofni
end
