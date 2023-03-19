include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "wceq.mm"
include "eqid.mm"
include "grpsubval.mm"
include "anidms.mm"
include "adantl.mm"
include "grprinv.mm"
include "eqtrd.mm"

theorem grpsubid
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let c.0: class .0.
  assume grpsubid.b: |- B = ( Base ` G )
  assume grpsubid.o: |- .0. = ( 0g ` G )
  assume grpsubid.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Grp /\ X e. B ) -> ( X .- X ) = .0. )

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
    cX
    cX
    c.mi
    co
    #
    cX
    cX
    cG
    cminusg
    cfv
    #
    cfv
    cG
    cplusg
    cfv
    #
    co
    #
    c.0
    @1
    @2
    @5
    wceq
    #
    @0
    @1
    @6
    cB
    @4
    cG
    @3
    c.mi
    cX
    cX
    grpsubid.b
    @4
    eqid
    #
    @3
    eqid
    #
    grpsubid.m
    grpsubval
    anidms
    adantl
    cB
    @4
    cG
    @3
    cX
    c.0
    grpsubid.b
    @7
    grpsubid.o
    @8
    grprinv
    eqtrd
end
