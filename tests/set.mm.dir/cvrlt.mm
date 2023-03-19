include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wn.mm"
include "cvrval.mm"
include "simprbda.mm"

theorem cvrlt
  let cA: class A
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let cK: class K
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cvrfval.b: |- B = ( Base ` K )
  assume cvrfval.s: |- .< = ( lt ` K )
  assume cvrfval.c: |- C = ( <o ` K )


  assert |- ( ( ( K e. A /\ X e. B /\ Y e. B ) /\ X C Y ) -> X .< Y )

  proof
    cK
    cA
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    w3a
    cX
    cY
    cC
    wbr
    cX
    cY
    c.lt
    wbr
    cX
    vz
    cv
    #
    c.lt
    wbr
    @0
    cY
    c.lt
    wbr
    wa
    vz
    cB
    wrex
    wn
    vz
    cA
    cB
    cC
    c.lt
    cK
    cX
    cY
    cvrfval.b
    cvrfval.s
    cvrfval.c
    cvrval
    simprbda
end
