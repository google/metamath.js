include "cgrp.mm"
include "wcel.mm"
include "wne.mm"
include "cfv.mm"
include "wa.mm"
include "wceq.mm"
include "fveq2.mm"
include "adantl.mm"
include "grpinvinv.mm"
include "adantr.mm"
include "grpinvid.mm"
include "ad2antrr.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "necon3d.mm"
include "3impia.mm"

theorem grpinvnz
  let cB: class B
  let cG: class G
  let cN: class N
  let cX: class X
  let c.0: class .0.
  assume grpinvnzcl.b: |- B = ( Base ` G )
  assume grpinvnzcl.z: |- .0. = ( 0g ` G )
  assume grpinvnzcl.n: |- N = ( invg ` G )


  assert |- ( ( G e. Grp /\ X e. B /\ X =/= .0. ) -> ( N ` X ) =/= .0. )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    cX
    c.0
    wne
    cX
    cN
    cfv
    #
    c.0
    wne
    @0
    @1
    wa
    #
    @2
    c.0
    cX
    c.0
    @3
    @2
    c.0
    wceq
    #
    cX
    c.0
    wceq
    @3
    @4
    wa
    @2
    cN
    cfv
    #
    c.0
    cN
    cfv
    #
    cX
    c.0
    @4
    @5
    @6
    wceq
    @3
    @2
    c.0
    cN
    fveq2
    adantl
    @3
    @5
    cX
    wceq
    @4
    cB
    cG
    cN
    cX
    grpinvnzcl.b
    grpinvnzcl.n
    grpinvinv
    adantr
    @0
    @6
    c.0
    wceq
    @1
    @4
    cG
    cN
    c.0
    grpinvnzcl.z
    grpinvnzcl.n
    grpinvid
    ad2antrr
    3eqtr3d
    ex
    necon3d
    3impia
end
