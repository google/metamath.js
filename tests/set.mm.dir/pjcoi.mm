include "cpjh.mm"
include "cfv.mm"
include "pjfi.mm"
include "hocoi.mm"

theorem pjcoi
  let cA: class A
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH


  assert |- ( A e. ~H -> ( ( ( projh ` G ) o. ( projh ` H ) ) ` A ) = ( ( projh ` G ) ` ( ( projh ` H ) ` A ) ) )

  proof
    cA
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
    hocoi
end
