include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "wss.mm"
include "wceq.mm"
include "lss0ss.mm"
include "biantrud.mm"
include "eqss.mm"
include "syl6bbr.mm"

theorem lssle0
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


  assert |- ( ( W e. LMod /\ X e. S ) -> ( X C_ { .0. } <-> X = { .0. } ) )

  proof
    cW
    clmod
    wcel
    cX
    cS
    wcel
    wa
    #
    cX
    c.0
    csn
    #
    wss
    #
    @2
    @1
    cX
    wss
    #
    wa
    cX
    @1
    wceq
    @0
    @3
    @2
    cS
    cW
    cX
    c.0
    lss0cl.z
    lss0cl.s
    lss0ss
    biantrud
    cX
    @1
    eqss
    syl6bbr
end
