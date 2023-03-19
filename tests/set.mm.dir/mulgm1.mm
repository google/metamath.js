include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "co.mm"
include "cfv.mm"
include "cz.mm"
include "wceq.mm"
include "1z.mm"
include "mulgneg.mm"
include "mp3an2.mm"
include "mulg1.mm"
include "adantl.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem mulgm1
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cI: class I
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  assume mulgnncl.b: |- B = ( Base ` G )
  assume mulgnncl.t: |- .x. = ( .g ` G )
  assume mulgneg.i: |- I = ( invg ` G )


  assert |- ( ( G e. Grp /\ X e. B ) -> ( -u 1 .x. X ) = ( I ` X ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    c1
    cneg
    cX
    c.x
    co
    #
    c1
    cX
    c.x
    co
    #
    cI
    cfv
    #
    cX
    cI
    cfv
    @0
    c1
    cz
    wcel
    @1
    @3
    @5
    wceq
    1z
    cB
    c.x
    cG
    cI
    c1
    cX
    mulgnncl.b
    mulgnncl.t
    mulgneg.i
    mulgneg
    mp3an2
    @2
    @4
    cX
    cI
    @1
    @4
    cX
    wceq
    @0
    cB
    c.x
    cG
    cX
    mulgnncl.b
    mulgnncl.t
    mulg1
    adantl
    fveq2d
    eqtrd
end
