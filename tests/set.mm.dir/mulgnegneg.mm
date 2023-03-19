include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cneg.mm"
include "co.mm"
include "cfv.mm"
include "mulgneg.mm"
include "fveq2d.mm"
include "wceq.mm"
include "simp1.mm"
include "mulgcl.mm"
include "grpinvinv.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem mulgnegneg
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cI: class I
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume mulgnncl.b: |- B = ( Base ` G )
  assume mulgnncl.t: |- .x. = ( .g ` G )
  assume mulgneg.i: |- I = ( invg ` G )


  assert |- ( ( G e. Grp /\ N e. ZZ /\ X e. B ) -> ( I ` ( -u N .x. X ) ) = ( N .x. X ) )

  proof
    cG
    cgrp
    wcel
    #
    cN
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cN
    cneg
    cX
    c.x
    co
    #
    cI
    cfv
    cN
    cX
    c.x
    co
    #
    cI
    cfv
    #
    cI
    cfv
    #
    @5
    @3
    @4
    @6
    cI
    cB
    c.x
    cG
    cI
    cN
    cX
    mulgnncl.b
    mulgnncl.t
    mulgneg.i
    mulgneg
    fveq2d
    @3
    @0
    @5
    cB
    wcel
    @7
    @5
    wceq
    @0
    @1
    @2
    simp1
    cB
    c.x
    cG
    cN
    cX
    mulgnncl.b
    mulgnncl.t
    mulgcl
    cB
    cG
    cI
    @5
    mulgnncl.b
    mulgneg.i
    grpinvinv
    syl2anc
    eqtrd
end
