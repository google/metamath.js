include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "wceq.mm"
include "id.mm"
include "grpidcl.mm"
include "eqid.mm"
include "grpsubval.mm"
include "syl2anr.mm"
include "grpinvid.mm"
include "adantr.mm"
include "oveq2d.mm"
include "grprid.mm"
include "3eqtrd.mm"

theorem grpsubid1
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let c.0: class .0.
  assume grpsubid.b: |- B = ( Base ` G )
  assume grpsubid.o: |- .0. = ( 0g ` G )
  assume grpsubid.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Grp /\ X e. B ) -> ( X .- .0. ) = X )

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
    cX
    c.0
    c.mi
    co
    #
    cX
    c.0
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cX
    c.0
    @6
    co
    cX
    @1
    @1
    c.0
    cB
    wcel
    @3
    @7
    wceq
    @0
    @1
    id
    cB
    cG
    c.0
    grpsubid.b
    grpsubid.o
    grpidcl
    cB
    @6
    cG
    @4
    c.mi
    cX
    c.0
    grpsubid.b
    @6
    eqid
    #
    @4
    eqid
    #
    grpsubid.m
    grpsubval
    syl2anr
    @2
    @5
    c.0
    cX
    @6
    @0
    @5
    c.0
    wceq
    @1
    cG
    @4
    c.0
    grpsubid.o
    @9
    grpinvid
    adantr
    oveq2d
    cB
    @6
    cG
    cX
    c.0
    grpsubid.b
    @8
    grpsubid.o
    grprid
    3eqtrd
end
