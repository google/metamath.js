include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "lss0cl.mm"
include "snssd.mm"

theorem lss0ss
  let cS: class S
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let cU: class U
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  assume lss0cl.z: |- .0. = ( 0g ` W )
  assume lss0cl.s: |- S = ( LSubSp ` W )


  assert |- ( ( W e. LMod /\ X e. S ) -> { .0. } C_ X )

  proof
    cW
    clmod
    wcel
    cX
    cS
    wcel
    wa
    c.0
    cX
    cS
    cX
    cW
    c.0
    lss0cl.z
    lss0cl.s
    lss0cl
    snssd
end
